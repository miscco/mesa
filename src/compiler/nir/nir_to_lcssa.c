/*
 * Copyright © 2015 Thomas Helland
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
 */

/*
 * This pass converts the ssa-graph into "Loop Closed SSA form". This is
 * done by placing phi nodes at the exits of the loop for all values
 * that are used outside the loop. The result is it transforms:
 *
 * loop {                    ->      loop {
 *    ssa2 = ....            ->          ssa2 = ...
 *    if (cond)              ->          if (cond)
 *       break;              ->             break;
 *    ssa3 = ssa2 * ssa4     ->          ssa3 = ssa2 * ssa4
 * }                         ->       }
 * ssa6 = ssa2 + 4           ->       ssa5 = phi(ssa2)
 *                                    ssa6 = ssa5 + 4
 */

#include "nir.h"

typedef struct {
   /* The nir_shader we are transforming */
   nir_shader *shader;

   /* The loop we store information for */
   nir_loop *loop;

   /* Whether to skip loop invariant variables */
   bool skip_invariants;
} lcssa_state;

static bool
is_if_use_inside_loop(nir_src *use, nir_loop *loop)
{
   nir_block *block_before_loop =
      nir_cf_node_as_block(nir_cf_node_prev(&loop->cf_node));
   nir_block *block_after_loop =
      nir_cf_node_as_block(nir_cf_node_next(&loop->cf_node));

   nir_block *prev_block =
      nir_cf_node_as_block(nir_cf_node_prev(&use->parent_if->cf_node));
   if (prev_block->index <= block_before_loop->index ||
       prev_block->index >= block_after_loop->index) {
      return false;
   }

   return true;
}

static bool
is_use_inside_loop(nir_src *use, nir_loop *loop)
{
   nir_block *block_before_loop =
      nir_cf_node_as_block(nir_cf_node_prev(&loop->cf_node));
   nir_block *block_after_loop =
      nir_cf_node_as_block(nir_cf_node_next(&loop->cf_node));

   if (use->parent_instr->block->index <= block_before_loop->index ||
       use->parent_instr->block->index >= block_after_loop->index) {
      return false;
   }

   return true;
}

static bool
is_defined_before_loop(nir_ssa_def *def, nir_loop *loop)
{
   nir_instr *instr = def->parent_instr;
   nir_block *block_before_loop =
      nir_cf_node_as_block(nir_cf_node_prev(&loop->cf_node));

   if (instr->block->index <= block_before_loop->index)
      return true;

   return false;
}

typedef enum instr_invariance {
   undefined = 0,
   invariant,
   not_invariant,
} instr_invariance;

static instr_invariance
instr_is_invariant(nir_instr *instr, nir_loop *loop);

static instr_invariance
def_is_invariant(nir_ssa_def *def, nir_loop *loop)
{
   if (is_defined_before_loop(def, loop))
      return invariant;

   if (def->parent_instr->pass_flags == undefined)
      def->parent_instr->pass_flags = instr_is_invariant(def->parent_instr, loop);

   return def->parent_instr->pass_flags;
}

static bool
src_is_invariant(nir_src *src, void *state)
{
   assert(src->is_ssa);
   return def_is_invariant(src->ssa, (nir_loop *)state) == invariant;
}

static instr_invariance
instr_is_invariant(nir_instr *instr, nir_loop *loop)
{
   assert(instr->pass_flags == undefined);

   switch (instr->type) {
   case nir_instr_type_load_const:
   case nir_instr_type_ssa_undef: {
      return invariant;
   }
   case nir_instr_type_call: {
      return not_invariant;
   }
   case nir_instr_type_phi: {
      /* base case: it's a phi at the loop header */
      if (instr->block == nir_loop_first_block(loop))
         return not_invariant;

      /* break potential cycles */
      instr->pass_flags = invariant;

      nir_phi_instr *phi = nir_instr_as_phi(instr);

      nir_foreach_phi_src(src, phi) {
         if (def_is_invariant(src->src.ssa, loop) == not_invariant)
            return not_invariant;
      }
      return invariant;
   }
   case nir_instr_type_intrinsic: {
      nir_intrinsic_instr *intrinsic = nir_instr_as_intrinsic(instr);
      if (!(nir_intrinsic_infos[intrinsic->intrinsic].flags & NIR_INTRINSIC_CAN_REORDER))
         return not_invariant;
      /* fallthrough */
   }
   default: {
      return nir_foreach_src(instr, src_is_invariant, loop) ? invariant : not_invariant;
   }
   }

   return invariant;
}

static void
prepare_loop_invariance(nir_cf_node *cf_node)
{
   nir_foreach_block_in_cf_node(block, cf_node) {
      nir_foreach_instr(instr, block)
         instr->pass_flags = undefined;
   }

   nir_foreach_block_in_cf_node(block, cf_node) {
      nir_foreach_instr(instr, block)
         if (instr->pass_flags == undefined)
            instr->pass_flags = instr_is_invariant(instr, nir_cf_node_as_loop(cf_node));
   }
}


static bool
convert_loop_exit_for_ssa(nir_ssa_def *def, void *void_state)
{
   lcssa_state *state = void_state;
   bool all_uses_inside_loop = true;

   /* Don't create LCSSA-Phis for loop-invariant variables */
   if (state->skip_invariants) {
      assert(def->parent_instr->pass_flags != undefined);
      if (def->parent_instr->pass_flags == invariant)
         return true;
   }

   nir_block *block_after_loop =
      nir_cf_node_as_block(nir_cf_node_next(&state->loop->cf_node));

   nir_foreach_use(use, def) {
      if (use->parent_instr->type == nir_instr_type_phi &&
          use->parent_instr->block == block_after_loop) {
         continue;
      }

      if (!is_use_inside_loop(use, state->loop)) {
         all_uses_inside_loop = false;
      }
   }

   nir_foreach_if_use(use, def) {
      if (!is_if_use_inside_loop(use, state->loop)) {
         all_uses_inside_loop = false;
      }
   }

   /* There where no sources that had defs outside the loop */
   if (all_uses_inside_loop)
      return true;

   /* We don't want derefs ending up in phi sources */
   if (def->parent_instr->type == nir_instr_type_deref)
      return true;

   /* Initialize a phi-instruction */
   nir_phi_instr *phi = nir_phi_instr_create(state->shader);
   nir_ssa_dest_init(&phi->instr, &phi->dest,
                     def->num_components, def->bit_size, "LCSSA-phi");

   /* Create a phi node with as many sources pointing to the same ssa_def as
    * the block has predecessors.
    */
   set_foreach(block_after_loop->predecessors, entry) {
      nir_phi_src *phi_src = ralloc(phi, nir_phi_src);
      phi_src->src = nir_src_for_ssa(def);
      phi_src->pred = (nir_block *) entry->key;

      exec_list_push_tail(&phi->srcs, &phi_src->node);
   }

   nir_instr_insert_before_block(block_after_loop, &phi->instr);

   /* Run through all uses and rewrite those outside the loop to point to
    * the phi instead of pointing to the ssa-def.
    */
   nir_foreach_use_safe(use, def) {
      if (use->parent_instr->type == nir_instr_type_phi &&
          block_after_loop == use->parent_instr->block) {
         continue;
      }

      if (!is_use_inside_loop(use, state->loop)) {
         nir_instr_rewrite_src(use->parent_instr, use,
                               nir_src_for_ssa(&phi->dest.ssa));
      }
   }

   nir_foreach_if_use_safe(use, def) {
      if (!is_if_use_inside_loop(use, state->loop)) {
         nir_if_rewrite_condition(use->parent_if,
                                  nir_src_for_ssa(&phi->dest.ssa));
      }
   }

   return true;
}

static void
convert_to_lcssa(nir_cf_node *cf_node, lcssa_state *state)
{
   switch (cf_node->type) {
   case nir_cf_node_block:
      return;
   case nir_cf_node_if: {
      nir_if *if_stmt = nir_cf_node_as_if(cf_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->then_list)
         convert_to_lcssa(nested_node, state);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->else_list)
         convert_to_lcssa(nested_node, state);
      return;
   }
   case nir_cf_node_loop: {
      /* first, convert inner loops */
      nir_loop *loop = nir_cf_node_as_loop(cf_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &loop->body)
         convert_to_lcssa(nested_node, state);

      if (state->skip_invariants)
         prepare_loop_invariance(cf_node);

      state->loop = loop;
      nir_foreach_block_in_cf_node(block, cf_node) {
         nir_foreach_instr(instr, block)
            nir_foreach_ssa_def(instr, convert_loop_exit_for_ssa, state);
      }

      return;
   }
   default:
      unreachable("unknown cf node type");
   }
}

void
nir_convert_loop_to_lcssa(nir_loop *loop) {
   nir_function_impl *impl = nir_cf_node_get_function(&loop->cf_node);

   nir_metadata_require(impl, nir_metadata_block_index);

   lcssa_state *state = rzalloc(NULL, lcssa_state);
   state->loop = loop;
   state->shader = impl->function->shader;
   state->skip_invariants = false;

   nir_foreach_block_in_cf_node (block, &loop->cf_node) {
      nir_foreach_instr(instr, block)
         nir_foreach_ssa_def(instr, convert_loop_exit_for_ssa, state);
   }

   ralloc_free(state);
}

void
nir_to_lcssa(nir_shader *shader) {

   lcssa_state *state = rzalloc(NULL, lcssa_state);
   state->shader = shader;
   state->skip_invariants = true;

   nir_foreach_function(function, shader) {
      if (function->impl == NULL) 
         continue;

      foreach_list_typed(nir_cf_node, node, node, &function->impl->body)
         convert_to_lcssa(node, state);
   }

   ralloc_free(state);
}
