/*
 * Copyright © 2019 Valve Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice (including the next
 * paragraph) shall be included in all copies or substantial portions of the
 * Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 *
 */

#include <vector>

#include "aco_ir.h"
#include "aco_builder.h"

namespace aco {

namespace {

enum WQMState : uint8_t {
   Unspecified = 0,
   Exact = 1 << 0,
   WQM = 1 << 1, /* with control flow applied */
   Preserve_WQM = 1 << 2,
};

enum mask_type : uint8_t {
   mask_type_global = 1 << 0,
   mask_type_exact = 1 << 1,
   mask_type_wqm = 1 << 2,
   mask_type_loop = 1 << 3, /* active lanes of a loop */
};

struct wqm_ctx {
   Program* program;
   /* state for WQM propagation */
   std::set<unsigned> worklist;
   std::vector<uint16_t> defined_in;
   std::vector<bool> needs_wqm;
   std::vector<bool> branch_wqm; /* true if the branch condition in this block should be in wqm */
   wqm_ctx(Program* program) : program(program),
                               defined_in(program->peekAllocationId(), 0xFFFF),
                               needs_wqm(program->peekAllocationId()),
                               branch_wqm(program->blocks.size())
   {
      for (unsigned i = 0; i < program->blocks.size(); i++)
         worklist.insert(i);
   }
};

struct loop_info {
   Block* loop_header;
   uint16_t num_exec_masks;
   uint8_t needs;
   bool has_divergent_break;
   bool has_divergent_continue;
   bool has_discard;
   loop_info(Block* b, uint16_t num, uint8_t needs, bool breaks, bool cont, bool discard) :
             loop_header(b), num_exec_masks(num), needs(needs), has_divergent_break(breaks),
             has_divergent_continue(cont), has_discard(discard) {}
};

struct block_info {
   std::vector<std::pair<Temp, uint8_t>> exec;
   std::vector<WQMState> instr_needs;
   uint8_t block_needs;
   uint8_t ever_again_needs;
   /* more... */
};

struct exec_ctx {
   Program *program;
   std::vector<block_info> info;
   std::vector<loop_info> loop;
   bool handle_wqm = false;
   exec_ctx(Program *program) : program(program), info(program->blocks.size()) {}
};

bool pred_by_exec_mask(aco_ptr<Instruction>& instr) {
   if (instr->format == Format::SMEM || instr->isSALU())
      return false;
   if (instr->format == Format::PSEUDO_BARRIER)
      return false;

   if (instr->format == Format::PSEUDO) {
      switch (instr->opcode) {
      case aco_opcode::p_create_vector:
         return instr->getDefinition(0).getTemp().type() == RegType::vgpr;
      case aco_opcode::p_extract_vector:
      case aco_opcode::p_split_vector:
         return instr->getOperand(0).getTemp().type() == RegType::vgpr;
      case aco_opcode::p_spill:
      case aco_opcode::p_reload:
         return false;
      default:
         break;
      }
   }

   if (instr->opcode == aco_opcode::v_readlane_b32 ||
       instr->opcode == aco_opcode::v_writelane_b32)
      return false;

   return true;
}

bool needs_exact(aco_ptr<Instruction>& instr) {
   if (instr->format == Format::MUBUF) {
      MUBUF_instruction *mubuf = static_cast<MUBUF_instruction *>(instr.get());
      return mubuf->disable_wqm;
   } else if (instr->format == Format::MIMG) {
      MIMG_instruction *mimg = static_cast<MIMG_instruction *>(instr.get());
      return mimg->disable_wqm;
   } else {
      return instr->opcode == aco_opcode::p_fs_buffer_store_smem;
   }
}

void set_needs_wqm(wqm_ctx &ctx, Temp tmp)
{
   if (!ctx.needs_wqm[tmp.id()]) {
      ctx.needs_wqm[tmp.id()] = true;
      if (ctx.defined_in[tmp.id()] != 0xFFFF)
         ctx.worklist.insert(ctx.defined_in[tmp.id()]);
   }
}

void mark_block_wqm(wqm_ctx &ctx, unsigned block_idx)
{
   if (ctx.branch_wqm[block_idx])
      return;

   ctx.branch_wqm[block_idx] = true;
   Block& block = ctx.program->blocks[block_idx];
   aco_ptr<Instruction>& branch = block.instructions.back();

   if (branch->opcode != aco_opcode::p_branch) {
      assert(branch->operandCount() && branch->getOperand(0).isTemp());
      set_needs_wqm(ctx, branch->getOperand(0).getTemp());
   }

   /* TODO: this sets more branch conditions to WQM than it needs to
    * it should be enough to stop at the "exec mask top level" */
   if (block.kind & block_kind_top_level)
      return;

   for (unsigned pred_idx : block.logical_preds)
      mark_block_wqm(ctx, pred_idx);
}

void get_block_needs(wqm_ctx &ctx, block_info& info, Block* block)
{
   std::vector<WQMState> instr_needs(block->instructions.size());

   for (int i = block->instructions.size() - 1; i >= 0; --i)
   {
      aco_ptr<Instruction>& instr = block->instructions[i];

      WQMState needs = needs_exact(instr) ? Exact : Unspecified;
      bool propagate_wqm = instr->opcode == aco_opcode::p_wqm;
      bool preserve_wqm = instr->opcode == aco_opcode::p_discard_if;
      bool pred_by_exec = pred_by_exec_mask(instr);
      for (unsigned j = 0; j < instr->definitionCount(); j++) {
         if (!instr->getDefinition(j).isTemp())
            continue;
         unsigned def = instr->getDefinition(j).tempId();
         ctx.defined_in[def] = block->index;
         if (needs == Unspecified && ctx.needs_wqm[def]) {
            needs = pred_by_exec ? WQM : Unspecified;
            propagate_wqm = true;
         }
      }

      if (propagate_wqm) {
         for (unsigned j = 0; j < instr->operandCount(); j++) {
            if (!instr->getOperand(j).isTemp())
               continue;
            set_needs_wqm(ctx, instr->getOperand(j).getTemp());
         }
      } else if (preserve_wqm && info.block_needs & WQM) {
         needs = Preserve_WQM;
      }

      /* ensure the condition controlling the control flow for this phi is in WQM */
      if (needs == WQM && instr->opcode == aco_opcode::p_phi) {
         for (unsigned pred_idx : block->logical_preds)
            mark_block_wqm(ctx, pred_idx);
      }

      instr_needs[i] = needs;
      info.block_needs |= needs;
   }
   /* for "if (<cond>) <wqm code>" or "while (<cond>) <wqm code>",
    * <cond> should be computed in WQM */
   if (info.block_needs & WQM && !(block->kind & block_kind_top_level)) {
      for (unsigned pred_idx : block->logical_preds)
         mark_block_wqm(ctx, pred_idx);
   }

   info.instr_needs = instr_needs;
}

void calculate_wqm_needs(exec_ctx& exec_ctx)
{
   wqm_ctx ctx(exec_ctx.program);

   while (!ctx.worklist.empty()) {
      unsigned block_index = *std::prev(ctx.worklist.end());
      ctx.worklist.erase(std::prev(ctx.worklist.end()));

      Block *block = &exec_ctx.program->blocks[block_index];
      get_block_needs(ctx, exec_ctx.info[block_index], block);
   }

   uint8_t ever_again_needs = 0;
   for (int i = exec_ctx.program->blocks.size() - 1; i >= 0; i--) {
      exec_ctx.info[i].ever_again_needs = ever_again_needs;
      Block& block = exec_ctx.program->blocks[i];

      if (block.kind & block_kind_needs_lowering)
         exec_ctx.info[i].block_needs |= Exact;

      /* if discard is used somewhere in nested CF, we need to preserve the WQM mask */
      if ((block.kind & block_kind_discard ||
           block.kind & block_kind_uses_discard_if) &&
          ever_again_needs & WQM)
         exec_ctx.info[i].block_needs |= Preserve_WQM;

      ever_again_needs |= exec_ctx.info[i].block_needs;
      if (block.kind & block_kind_discard ||
          block.kind & block_kind_uses_discard_if)
         ever_again_needs |= Exact;

      /* don't propagate WQM preservation further than the next top_level block */
      if (block.kind & block_kind_top_level)
         ever_again_needs &= ~Preserve_WQM;
      else
         exec_ctx.info[i].block_needs &= ~Preserve_WQM;
   }
   exec_ctx.handle_wqm = true;
}

void transition_to_WQM(exec_ctx& ctx, Builder bld, unsigned idx)
{
   if (ctx.info[idx].exec.back().second & mask_type_wqm)
      return;
   if (ctx.info[idx].exec.back().second & mask_type_global) {
      Temp exec_mask = ctx.info[idx].exec.back().first;
      exec_mask = bld.sop1(aco_opcode::s_wqm_b64, bld.def(s2, exec), bld.def(s1, scc), bld.exec(exec_mask));
      ctx.info[idx].exec.emplace_back(exec_mask, mask_type_global | mask_type_wqm);
      return;
   }
   /* otherwise, the WQM mask should be one below the current mask */
   ctx.info[idx].exec.pop_back();
   assert(ctx.info[idx].exec.back().second & mask_type_wqm);
   ctx.info[idx].exec.back().first = bld.pseudo(aco_opcode::p_parallelcopy, bld.def(s2, exec),
                                                ctx.info[idx].exec.back().first);
}

void transition_to_Exact(exec_ctx& ctx, Builder bld, unsigned idx)
{
   if (ctx.info[idx].exec.back().second & mask_type_exact)
      return;
   if (ctx.info[idx].exec.back().second & mask_type_global) {
      ctx.info[idx].exec.pop_back();
      assert(ctx.info[idx].exec.back().second & mask_type_exact);
      ctx.info[idx].exec.back().first = bld.pseudo(aco_opcode::p_parallelcopy, bld.def(s2, exec),
                                                   ctx.info[idx].exec.back().first);
      return;
   }
   /* otherwise, we create an exact mask and push to the stack */
   Temp wqm = ctx.info[idx].exec.back().first;
   Temp exact = bld.tmp(s2);
   wqm = bld.sop1(aco_opcode::s_and_saveexec_b64, bld.def(s2), bld.def(s1, scc),
                  bld.exec(Definition(exact)), ctx.info[idx].exec[0].first, bld.exec(wqm));
   ctx.info[idx].exec.back().first = wqm;
   ctx.info[idx].exec.emplace_back(exact, mask_type_exact);
}

unsigned add_coupling_code(exec_ctx& ctx, Block* block,
                           std::vector<aco_ptr<Instruction>>& instructions)
{
   unsigned idx = block->index;
   Builder bld(ctx.program, &instructions);
   std::vector<unsigned>& preds = block->linear_preds;

   /* start block */
   if (idx == 0) {
      aco_ptr<Instruction>& startpgm = block->instructions[0];
      assert(startpgm->opcode == aco_opcode::p_startpgm);
      Temp exec_mask = startpgm->getDefinition(startpgm->num_definitions - 1).getTemp();
      bld.insert(std::move(startpgm));

      if (ctx.handle_wqm) {
         ctx.info[0].exec.emplace_back(exec_mask, mask_type_global | mask_type_exact);
         /* if this block only needs WQM, initialize already */
         if (ctx.info[0].block_needs == WQM)
            transition_to_WQM(ctx, bld, 0);
      } else {
         if (ctx.program->needs_wqm)
            exec_mask = bld.sop1(aco_opcode::s_wqm_b64, bld.def(s2, exec), bld.def(s1, scc), bld.exec(exec_mask));
         ctx.info[0].exec.emplace_back(exec_mask, mask_type_global);
      }

      return 1;
   }

   /* loop entry block */
   if (block->kind & block_kind_loop_header) {
      assert(preds[0] == idx - 1);
      ctx.info[idx].exec = ctx.info[idx - 1].exec;
      loop_info& info = ctx.loop.back();
      assert(ctx.info[idx].exec.size() == info.num_exec_masks);

      /* create ssa names for outer exec masks */
      if (info.has_discard) {
         aco_ptr<Pseudo_instruction> phi;
         for (int i = 0; i < info.num_exec_masks - 1; i++) {
            phi.reset(create_instruction<Pseudo_instruction>(aco_opcode::p_linear_phi, Format::PSEUDO, preds.size(), 1));
            phi->getDefinition(0) = bld.def(s2);
            phi->getOperand(0) = Operand(ctx.info[preds[0]].exec[i].first);
            ctx.info[idx].exec[i].first = bld.insert(std::move(phi));
         }
      }

      /* create ssa name for restore mask */
      if (info.has_divergent_break) {
         /* this phi might be trivial but ensures a parallelcopy on the loop header */
         aco_ptr<Pseudo_instruction> phi{create_instruction<Pseudo_instruction>(aco_opcode::p_linear_phi, Format::PSEUDO, preds.size(), 1)};
         phi->getDefinition(0) = bld.def(s2);
         phi->getOperand(0) = Operand(ctx.info[preds[0]].exec.back().first);
         ctx.info[idx].exec.back().first = bld.insert(std::move(phi));
      }

      /* create ssa name for loop active mask */
      aco_ptr<Pseudo_instruction> phi{create_instruction<Pseudo_instruction>(aco_opcode::p_linear_phi, Format::PSEUDO, preds.size(), 1)};
      if (info.has_divergent_continue)
         phi->getDefinition(0) = bld.def(s2);
      else
         phi->getDefinition(0) = bld.def(s2, exec);
      phi->getOperand(0) = Operand(ctx.info[preds[0]].exec.back().first);
      Temp loop_active = bld.insert(std::move(phi));

      if (info.has_divergent_break) {
         uint8_t mask_type = (ctx.info[idx].exec.back().second & ~mask_type_global) | mask_type_loop;
         ctx.info[idx].exec.emplace_back(loop_active, mask_type);
      } else {
         ctx.info[idx].exec.back().first = loop_active;
         ctx.info[idx].exec.back().second |= mask_type_loop;
      }

      /* create a parallelcopy to move the active mask to exec */
      unsigned i = 0;
      if (info.has_divergent_continue) {
         while (block->instructions[i]->opcode != aco_opcode::p_logical_start) {
            bld.insert(std::move(block->instructions[i]));
            i++;
         }
         uint8_t mask_type = ctx.info[idx].exec.back().second & (mask_type_wqm | mask_type_exact);
         ctx.info[idx].exec.emplace_back(bld.pseudo(aco_opcode::p_parallelcopy, bld.def(s2, exec),
                                                    ctx.info[idx].exec.back().first), mask_type);
      }

      return i;
   }

   /* loop exit block */
   if (block->kind & block_kind_loop_exit) {
      Block* header = ctx.loop.back().loop_header;
      loop_info& info = ctx.loop.back();
      unsigned num_exec_masks = ctx.loop.back().num_exec_masks;

      for (MAYBE_UNUSED unsigned pred : preds)
         assert(ctx.info[pred].exec.size() >= num_exec_masks);

      /* fill the loop header phis */
      std::vector<unsigned>& header_preds = header->linear_preds;
      int k = 0;
      if (info.has_discard) {
         while (k < info.num_exec_masks - 1) {
            aco_ptr<Instruction>& phi = header->instructions[k];
            assert(phi->opcode == aco_opcode::p_linear_phi);
            for (unsigned i = 1; i < phi->num_operands; i++)
               phi->getOperand(i) = Operand(ctx.info[header_preds[i]].exec[k].first);
            k++;
         }
      }
      aco_ptr<Instruction>& phi = header->instructions[k++];
      assert(phi->opcode == aco_opcode::p_linear_phi);
      for (unsigned i = 1; i < phi->num_operands; i++)
         phi->getOperand(i) = Operand(ctx.info[header_preds[i]].exec[info.num_exec_masks - 1].first);

      if (info.has_divergent_break) {
         aco_ptr<Instruction>& phi = header->instructions[k];
         assert(phi->opcode == aco_opcode::p_linear_phi);
         for (unsigned i = 1; i < phi->num_operands; i++)
            phi->getOperand(i) = Operand(ctx.info[header_preds[i]].exec[info.num_exec_masks].first);
      }

      /* create the loop exit phis if not trivial */
      for (unsigned k = 0; k < num_exec_masks; k++) {
         Temp same = ctx.info[preds[0]].exec[k].first;
         uint8_t type = ctx.info[header_preds[0]].exec[k].second;
         bool trivial = true;

         for (unsigned i = 1; i < preds.size() && trivial; i++) {
            if (ctx.info[preds[i]].exec[k].first != same)
               trivial = false;
         }

         if (trivial) {
            ctx.info[idx].exec.emplace_back(same, type);
         } else {
            /* create phi for loop footer */
            aco_ptr<Pseudo_instruction> phi{create_instruction<Pseudo_instruction>(aco_opcode::p_linear_phi, Format::PSEUDO, preds.size(), 1)};
            phi->getDefinition(0) = bld.def(s2);
            for (unsigned i = 0; i < phi->num_operands; i++)
               phi->getOperand(i) = Operand(ctx.info[preds[i]].exec[k].first);
            ctx.info[idx].exec.emplace_back(bld.insert(std::move(phi)), type);
         }
      }
      assert(ctx.info[idx].exec.size() == num_exec_masks);

      /* create a parallelcopy to move the live mask to exec */
      unsigned i = 0;
      while (block->instructions[i]->opcode != aco_opcode::p_logical_start) {
         bld.insert(std::move(block->instructions[i]));
         i++;
      }

      if (ctx.handle_wqm) {
         if (block->kind & block_kind_top_level && ctx.info[idx].exec.size() == 2) {
            if ((ctx.info[idx].block_needs | ctx.info[idx].ever_again_needs) == 0 ||
                (ctx.info[idx].block_needs | ctx.info[idx].ever_again_needs) == Exact) {
               ctx.info[idx].exec.back().second |= mask_type_global;
               ctx.handle_wqm = false;
            }
         }
         if (ctx.info[idx].block_needs == WQM)
            transition_to_WQM(ctx, bld, idx);
         else if (ctx.info[idx].block_needs == Exact)
            transition_to_Exact(ctx, bld, idx);
      }

      ctx.info[idx].exec.back().first = bld.pseudo(aco_opcode::p_parallelcopy, bld.def(s2, exec),
                                                   ctx.info[idx].exec.back().first);

      ctx.loop.pop_back();
      return i;
   }

   if (preds.size() == 1) {
      ctx.info[idx].exec = ctx.info[preds[0]].exec;
   } else {
      assert(preds.size() == 2);
      /* if one of the predecessors ends in exact mask, we pop it from stack */
      unsigned num_exec_masks = std::min(ctx.info[preds[0]].exec.size(),
                                         ctx.info[preds[1]].exec.size());

      /* create phis for diverged exec masks */
      for (unsigned i = 0; i < num_exec_masks; i++) {
         if (ctx.info[preds[0]].exec[i].first == ctx.info[preds[1]].exec[i].first) {
            assert(ctx.info[preds[0]].exec[i].second == ctx.info[preds[1]].exec[i].second);
            ctx.info[idx].exec.emplace_back(ctx.info[preds[0]].exec[i]);
            continue;
         }
         bool in_exec = i == num_exec_masks - 1 && !(block->kind & block_kind_merge);
         Temp phi = bld.pseudo(aco_opcode::p_linear_phi, in_exec ? bld.def(s2, exec) : bld.def(s2),
                               ctx.info[preds[0]].exec[i].first,
                               ctx.info[preds[1]].exec[i].first);
         uint8_t mask_type = ctx.info[preds[0]].exec[i].second & ctx.info[preds[1]].exec[i].second;
         ctx.info[idx].exec.emplace_back(phi, mask_type);
      }
   }

   unsigned i = 0;
   while (block->instructions[i]->opcode == aco_opcode::p_phi ||
          block->instructions[i]->opcode == aco_opcode::p_linear_phi) {
      bld.insert(std::move(block->instructions[i]));
      i++;
   }

   if (block->kind & block_kind_merge)
      ctx.info[idx].exec.pop_back();

   /* try to satisfy the block's needs */
   if (ctx.handle_wqm) {
      if (block->kind & block_kind_top_level && ctx.info[idx].exec.size() == 2) {
         if ((ctx.info[idx].block_needs | ctx.info[idx].ever_again_needs) == 0 ||
             (ctx.info[idx].block_needs | ctx.info[idx].ever_again_needs) == Exact) {
            ctx.info[idx].exec.back().second |= mask_type_global;
            ctx.handle_wqm = false;
         }
      }
      if (ctx.info[idx].block_needs == WQM)
         transition_to_WQM(ctx, bld, idx);
      else if (ctx.info[idx].block_needs == Exact)
         transition_to_Exact(ctx, bld, idx);
   }

   if (block->kind & block_kind_merge) {
      Temp restore = ctx.info[idx].exec.back().first;
      ctx.info[idx].exec.back().first = bld.pseudo(aco_opcode::p_parallelcopy, bld.def(s2, exec), restore);
   }

   return i;
}

void lower_fs_buffer_store_smem(Builder& bld, bool need_check, aco_ptr<Instruction>& instr, Temp cur_exec)
{
   Operand offset = instr->getOperand(1);
   if (need_check) {
      /* if exec is zero, then use UINT32_MAX as an offset and make this store a no-op */
      Temp nonempty = bld.sopc(aco_opcode::s_cmp_lg_u64, bld.def(s1, scc), cur_exec, Operand(0u));

      if (offset.isLiteral())
         offset = bld.sop1(aco_opcode::s_mov_b32, bld.def(s1), offset);

      offset = bld.sop2(aco_opcode::s_cselect_b32, bld.hint_m0(bld.def(s1)),
                        offset, Operand(UINT32_MAX), bld.scc(nonempty));
   } else if (offset.isConstant() && offset.constantValue() > 0xFFFFF) {
      offset = bld.sop1(aco_opcode::s_mov_b32, bld.hint_m0(bld.def(s1)), offset);
   }
   if (!offset.isConstant())
      offset.setFixed(m0);

   switch (instr->getOperand(2).size()) {
   case 1:
      instr->opcode = aco_opcode::s_buffer_store_dword;
      break;
   case 2:
      instr->opcode = aco_opcode::s_buffer_store_dwordx2;
      break;
   case 4:
      instr->opcode = aco_opcode::s_buffer_store_dwordx4;
      break;
   default:
      unreachable("Invalid SMEM buffer store size");
   }
   instr->getOperand(1) = offset;
   /* as_uniform() needs to be done here so it's done in exact mode and helper
    * lanes don't contribute. */
   instr->getOperand(2) = Operand(bld.as_uniform(instr->getOperand(2)));
}

void process_instructions(exec_ctx& ctx, Block* block,
                          std::vector<aco_ptr<Instruction>>& instructions,
                          unsigned idx)
{
   /* if the block doesn't need both, WQM and Exact, we can skip processing the instructions */
   bool process = ctx.handle_wqm ||
                  ctx.info[block->index].block_needs == (WQM | Exact) ||
                  block->kind & block_kind_uses_discard_if ||
                  block->kind & block_kind_needs_lowering;
   if (!process) {
      std::vector<aco_ptr<Instruction>>::iterator it = std::next(block->instructions.begin(), idx);
      instructions.insert(instructions.end(),
                          std::move_iterator<std::vector<aco_ptr<Instruction>>::iterator>(it),
                          std::move_iterator<std::vector<aco_ptr<Instruction>>::iterator>(block->instructions.end()));
      return;
   }

   Builder bld(ctx.program, &instructions);
   WQMState state;
   if (ctx.info[block->index].exec.back().second & mask_type_wqm)
      state = WQM;
   else {
      assert(!ctx.handle_wqm || ctx.info[block->index].exec.back().second & mask_type_exact);
      state = Exact;
   }

   for (; idx < block->instructions.size(); idx++) {
      aco_ptr<Instruction> instr = std::move(block->instructions[idx]);

      WQMState needs = ctx.handle_wqm ? ctx.info[block->index].instr_needs[idx] : Unspecified;

      if (instr->opcode == aco_opcode::p_discard_if) {
         if (ctx.info[block->index].block_needs & Preserve_WQM) {
            assert(block->kind & block_kind_top_level);
            transition_to_WQM(ctx, bld, block->index);
            ctx.info[block->index].exec.back().second &= ~mask_type_global;
         }
         unsigned num = ctx.info[block->index].exec.size();
         assert(num);
         Operand cond = instr->getOperand(0);
         instr.reset(create_instruction<Pseudo_instruction>(aco_opcode::p_discard_if, Format::PSEUDO, num + 1, num + 1));
         for (unsigned i = 0; i < num; i++) {
            instr->getOperand(i) = Operand(ctx.info[block->index].exec[i].first);
            if (i == num - 1)
               instr->getOperand(i).setFixed(exec);
            Temp new_mask = bld.tmp(s2);
            instr->getDefinition(i) = Definition(new_mask);
            ctx.info[block->index].exec[i].first = new_mask;
         }
         assert((ctx.info[block->index].exec[0].second & mask_type_wqm) == 0);
         instr->getDefinition(num - 1).setFixed(exec);
         instr->getOperand(num) = cond;
         instr->getDefinition(num) = bld.def(s1, scc);

      } else if (needs == WQM && state != WQM) {
         transition_to_WQM(ctx, bld, block->index);
         state = WQM;
      } else if (needs == Exact && state != Exact) {
         transition_to_Exact(ctx, bld, block->index);
         state = Exact;
      }

      if (instr->opcode == aco_opcode::p_is_helper) {
         Definition dst = instr->getDefinition(0);
         if (state == Exact) {
            instr.reset(create_instruction<SOP1_instruction>(aco_opcode::s_mov_b64, Format::SOP1, 1, 1));
            instr->getOperand(0) = Operand(0u);
            instr->getDefinition(0) = dst;
         } else {
            instr.reset(create_instruction<SOP2_instruction>(aco_opcode::s_andn2_b64, Format::SOP2, 2, 2));
            instr->getOperand(0) = Operand(ctx.info[block->index].exec.back().first); /* current exec */
            assert(ctx.info[block->index].exec[0].second & mask_type_exact);
            instr->getOperand(1) = Operand(ctx.info[block->index].exec[0].first);
            instr->getDefinition(0) = dst;
            instr->getDefinition(1) = bld.def(s1, scc);
         }
      } else if (instr->opcode == aco_opcode::p_fs_buffer_store_smem) {
         bool need_check = ctx.info[block->index].exec.size() != 1 &&
                           !(ctx.info[block->index].exec[ctx.info[block->index].exec.size() - 2].second & Exact);
         lower_fs_buffer_store_smem(bld, need_check, instr, ctx.info[block->index].exec.back().first);
      }

      bld.insert(std::move(instr));
   }
}

void add_branch_code(exec_ctx& ctx, Block* block)
{
   unsigned idx = block->index;
   Builder bld(ctx.program, block);

   if (idx == ctx.program->blocks.size() - 1)
      return;

   /* try to disable wqm handling */
   if (ctx.handle_wqm && block->kind & block_kind_top_level) {
      if (ctx.info[idx].exec.size() == 3) {
         assert(ctx.info[idx].exec[1].second == mask_type_wqm);
         ctx.info[idx].exec.pop_back();
      }
      assert(ctx.info[idx].exec.size() <= 2);

      if (ctx.info[idx].ever_again_needs == 0) {
         if (ctx.info[idx].exec.size() == 2) {
            ctx.info[idx].exec[0] = ctx.info[idx].exec[1];
            ctx.info[idx].exec.pop_back();
            //assert(ctx.info[idx].exec[0].second & mask_type_global);
         }
         ctx.handle_wqm = false;

      } else if (ctx.info[idx].ever_again_needs == Exact) {
         /* transition to Exact */
         aco_ptr<Instruction> branch = std::move(block->instructions.back());
         block->instructions.pop_back();
         ctx.info[idx].exec.back().second |= mask_type_global;
         transition_to_Exact(ctx, bld, idx);
         bld.insert(std::move(branch));
         ctx.handle_wqm = false;

      } else if (ctx.info[idx].block_needs & Preserve_WQM) {
         /* transition to WQM and remove global flag */
         aco_ptr<Instruction> branch = std::move(block->instructions.back());
         block->instructions.pop_back();
         transition_to_WQM(ctx, bld, idx);
         ctx.info[idx].exec.back().second &= ~mask_type_global;
         bld.insert(std::move(branch));
      }
      if (!(ctx.info[idx].ever_again_needs & Exact)) {
         /* transition to WQM and disable WQM handling */
         aco_ptr<Instruction> branch = std::move(block->instructions.back());
         block->instructions.pop_back();
         transition_to_WQM(ctx, bld, idx);
         bld.insert(std::move(branch));
         if (ctx.info[idx].exec.size() == 2) {
            ctx.info[idx].exec[0] = ctx.info[idx].exec[1];
            ctx.info[idx].exec.pop_back();
         }
         ctx.handle_wqm = false;
      }
   }

   if (block->kind & block_kind_loop_preheader) {
      /* collect information about the succeeding loop */
      bool has_divergent_break = false;
      bool has_divergent_continue = false;
      bool has_discard = false;
      uint8_t needs = 0;
      unsigned loop_nest_depth = ctx.program->blocks[idx + 1].loop_nest_depth;

      for (unsigned i = idx + 1; ctx.program->blocks[i].loop_nest_depth >= loop_nest_depth; i++) {
         Block& loop_block = ctx.program->blocks[i];
         needs |= ctx.info[i].block_needs;

         if (loop_block.kind & block_kind_uses_discard_if ||
             loop_block.kind & block_kind_discard)
            has_discard = true;
         if (loop_block.loop_nest_depth != loop_nest_depth)
            continue;

         if (loop_block.kind & block_kind_uniform)
            continue;
         else if (loop_block.kind & block_kind_break)
            has_divergent_break = true;
         else if (loop_block.kind & block_kind_continue)
            has_divergent_continue = true;
      }

      if (ctx.handle_wqm) {
         if (needs & WQM) {
            aco_ptr<Instruction> branch = std::move(block->instructions.back());
            block->instructions.pop_back();
            transition_to_WQM(ctx, bld, idx);
            bld.insert(std::move(branch));
         } else if (needs == Exact) {
            aco_ptr<Instruction> branch = std::move(block->instructions.back());
            block->instructions.pop_back();
            transition_to_Exact(ctx, bld, idx);
            bld.insert(std::move(branch));
         }
      }

      ctx.loop.emplace_back(&ctx.program->blocks[block->linear_succs[0]],
                            ctx.info[idx].exec.size(),
                            needs,
                            has_divergent_break,
                            has_divergent_continue,
                            has_discard);
   }

   if (block->kind & block_kind_discard) {
      /* create a discard_if() instruction with the exec mask as condition */
      unsigned num = 0;
      if (ctx.loop.size()) {
         /* if we're in a loop, only discard from the outer exec masks */
         num = ctx.loop.back().num_exec_masks;
      } else {
         num = ctx.info[idx].exec.size() - 1;
      }

      Temp cond = ctx.info[idx].exec.back().first;
      aco_ptr<Pseudo_instruction> discard{create_instruction<Pseudo_instruction>(aco_opcode::p_discard_if, Format::PSEUDO, num + 1, num + 1)};
      for (unsigned i = 0; i < num; i++) {
         discard->getOperand(i) = Operand(ctx.info[block->index].exec[i].first);
         Temp new_mask = bld.tmp(s2);
         discard->getDefinition(i) = Definition(new_mask);
         ctx.info[block->index].exec[i].first = new_mask;
      }
      assert((ctx.info[block->index].exec[0].second & mask_type_wqm) == 0);
      discard->getOperand(num) = bld.exec(cond);
      discard->getDefinition(num) = bld.def(s1, scc);

      assert(block->instructions.back()->format == Format::PSEUDO_BRANCH);
      aco_ptr<Instruction> branch = std::move(block->instructions.back());
      block->instructions.pop_back();
      bld.insert(std::move(discard));

      if (!ctx.loop.size()) {
         /* check if the successor is the merge block, otherwise set exec to 0 */
         // TODO: this could be done better by directly branching to the merge block
         Block& succ = ctx.program->blocks[block->linear_succs[0]];
         if (!(succ.kind & block_kind_invert || succ.kind & block_kind_merge)) {
            ctx.info[idx].exec.back().first = bld.sop1(aco_opcode::s_mov_b64, bld.def(s2, exec), Operand(0u));
         }
      }

      bld.insert(std::move(branch));
      /* no return here as it can be followed by a divergent break */
   }

   if (block->kind & block_kind_uniform) {
      Pseudo_branch_instruction* branch = static_cast<Pseudo_branch_instruction*>(block->instructions.back().get());
      if (branch->opcode == aco_opcode::p_branch) {
         branch->target[0] = block->linear_succs[0];
      } else {
         branch->target[0] = block->linear_succs[1];
         branch->target[1] = block->linear_succs[0];
      }
      return;
   }

   if (block->kind & block_kind_branch) {

      if (ctx.handle_wqm &&
          ctx.info[idx].exec.back().second & mask_type_exact &&
          !(ctx.info[idx].exec.back().second & mask_type_global)) {
         /* return to wqm before branching */
         ctx.info[idx].exec.pop_back();
      }

      // orig = s_and_saveexec_b64
      assert(block->linear_succs.size() == 2);
      assert(block->instructions.back()->opcode == aco_opcode::p_cbranch_z);
      Temp cond = block->instructions.back()->getOperand(0).getTemp();
      block->instructions.pop_back();
      Temp current_exec = ctx.info[idx].exec.back().first;
      uint8_t mask_type = ctx.info[idx].exec.back().second & (mask_type_wqm | mask_type_exact);

      Temp then_mask = bld.tmp(s2);
      Temp old_exec = bld.sop1(aco_opcode::s_and_saveexec_b64, bld.def(s2), bld.def(s1, scc),
                               bld.exec(Definition(then_mask)), cond, bld.exec(current_exec));

      ctx.info[idx].exec.back().first = old_exec;

      /* add next current exec to the stack */
      ctx.info[idx].exec.emplace_back(then_mask, mask_type);

      bld.branch(aco_opcode::p_cbranch_z, bld.exec(then_mask), block->linear_succs[1], block->linear_succs[0]);
      return;
   }

   if (block->kind & block_kind_invert) {
      // exec = s_andn2_b64 (original_exec, exec)
      assert(block->instructions.back()->opcode == aco_opcode::p_cbranch_nz);
      block->instructions.pop_back();
      Temp then_mask = ctx.info[idx].exec.back().first;
      uint8_t mask_type = ctx.info[idx].exec.back().second;
      ctx.info[idx].exec.pop_back();
      Temp orig_exec = ctx.info[idx].exec.back().first;
      Temp else_mask = bld.sop2(aco_opcode::s_andn2_b64, bld.def(s2, exec),
                                bld.def(s1, scc), orig_exec, bld.exec(then_mask));

      /* add next current exec to the stack */
      ctx.info[idx].exec.emplace_back(else_mask, mask_type);

      bld.branch(aco_opcode::p_cbranch_z, bld.exec(else_mask), block->linear_succs[1], block->linear_succs[0]);
      return;
   }

   if (block->kind & block_kind_break) {
      // loop_mask = s_andn2_b64 (loop_mask, exec)
      assert(block->instructions.back()->opcode == aco_opcode::p_branch);
      block->instructions.pop_back();

      Temp current_exec = ctx.info[idx].exec.back().first;
      Temp cond = Temp();
      for (int exec_idx = ctx.info[idx].exec.size() - 2; exec_idx >= 0; exec_idx--) {
         cond = bld.tmp(s1);
         Temp exec_mask = ctx.info[idx].exec[exec_idx].first;
         exec_mask = bld.sop2(aco_opcode::s_andn2_b64, bld.def(s2), bld.scc(Definition(cond)),
                              exec_mask, bld.exec(current_exec));
         ctx.info[idx].exec[exec_idx].first = exec_mask;
         if (ctx.info[idx].exec[exec_idx].second & mask_type_loop)
            break;
      }

      /* check if the successor is the merge block, otherwise set exec to 0 */
      // TODO: this could be done better by directly branching to the merge block
      unsigned succ_idx = ctx.program->blocks[block->linear_succs[1]].linear_succs[0];
      Block& succ = ctx.program->blocks[succ_idx];
      if (!(succ.kind & block_kind_invert || succ.kind & block_kind_merge)) {
         ctx.info[idx].exec.back().first = bld.sop1(aco_opcode::s_mov_b64, bld.def(s2, exec), Operand(0u));
      }

      bld.branch(aco_opcode::p_cbranch_nz, bld.scc(cond), block->linear_succs[1], block->linear_succs[0]);
      return;
   }

   if (block->kind & block_kind_continue) {
      assert(block->instructions.back()->opcode == aco_opcode::p_branch);
      block->instructions.pop_back();

      Temp current_exec = ctx.info[idx].exec.back().first;
      Temp cond = Temp();
      for (int exec_idx = ctx.info[idx].exec.size() - 2; exec_idx >= 0; exec_idx--) {
         if (ctx.info[idx].exec[exec_idx].second & mask_type_loop)
            break;
         cond = bld.tmp(s1);
         Temp exec_mask = ctx.info[idx].exec[exec_idx].first;
         exec_mask = bld.sop2(aco_opcode::s_andn2_b64, bld.def(s2), bld.scc(Definition(cond)),
                              exec_mask, bld.exec(current_exec));
         ctx.info[idx].exec[exec_idx].first = exec_mask;
      }
      assert(cond != Temp());

      /* check if the successor is the merge block, otherwise set exec to 0 */
      // TODO: this could be done better by directly branching to the merge block
      unsigned succ_idx = ctx.program->blocks[block->linear_succs[1]].linear_succs[0];
      Block& succ = ctx.program->blocks[succ_idx];
      if (!(succ.kind & block_kind_invert || succ.kind & block_kind_merge)) {
         ctx.info[idx].exec.back().first = bld.sop1(aco_opcode::s_mov_b64, bld.def(s2, exec), Operand(0u));
      }

      bld.branch(aco_opcode::p_cbranch_nz, bld.scc(cond), block->linear_succs[1], block->linear_succs[0]);
      return;
   }
}

void process_block(exec_ctx& ctx, Block* block)
{
   std::vector<aco_ptr<Instruction>> instructions;
   instructions.reserve(block->instructions.size());

   unsigned idx = add_coupling_code(ctx, block, instructions);

   assert(block->index != ctx.program->blocks.size() - 1 ||
          ctx.info[block->index].exec.size() <= 2);

   process_instructions(ctx, block, instructions, idx);

   block->instructions = std::move(instructions);

   add_branch_code(ctx, block);

   block->live_out_exec = ctx.info[block->index].exec.back().first;
}

} /* end namespace */


void insert_exec_mask(Program *program)
{
   exec_ctx ctx(program);

   if (program->needs_wqm && program->needs_exact)
      calculate_wqm_needs(ctx);

   for (Block& block : program->blocks)
      process_block(ctx, &block);

}

}

