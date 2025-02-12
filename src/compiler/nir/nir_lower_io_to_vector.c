/*
 * Copyright © 2019 Intel Corporation
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

#include "nir.h"
#include "nir_builder.h"
#include "nir_deref.h"

/** @file nir_lower_io_to_vector.c
 *
 * Merges compatible input/output variables residing in different components
 * of the same location. It's expected that further passes such as
 * nir_lower_io_to_temporaries will combine loads and stores of the merged
 * variables, producing vector nir_load_input/nir_store_output instructions
 * when all is said and done.
 */

#define MAX_SLOTS MAX2(MAX_VARYINGS_INCL_PATCH, FRAG_RESULT_MAX)

static const struct glsl_type *
resize_array_vec_type(const struct glsl_type *type, unsigned num_components)
{
   if (glsl_type_is_array(type)) {
      const struct glsl_type *arr_elem =
         resize_array_vec_type(glsl_get_array_element(type), num_components);
      return glsl_array_type(arr_elem, glsl_get_length(type), 0);
   } else {
      assert(glsl_type_is_vector_or_scalar(type));
      return glsl_vector_type(glsl_get_base_type(type), num_components);
   }
}

static bool
variable_can_rewrite(const nir_variable *var)
{
   /* Skip complex types we don't split in the first place */
   if (!glsl_type_is_vector_or_scalar(glsl_without_array(var->type)))
      return false;

   /* TODO: add 64/16bit support ? */
   if (glsl_get_bit_size(glsl_without_array(var->type)) != 32)
      return false;

   return true;
}

static bool
variables_can_merge(nir_shader *shader,
                    const nir_variable *a, const nir_variable *b,
                    bool same_array_structure)
{
   const struct glsl_type *a_type_tail = a->type;
   const struct glsl_type *b_type_tail = b->type;

   /* They must have the same array structure */
   if (same_array_structure) {
      while (glsl_type_is_array(a_type_tail)) {
         if (!glsl_type_is_array(b_type_tail))
            return false;

         if (glsl_get_length(a_type_tail) != glsl_get_length(b_type_tail))
            return false;

         a_type_tail = glsl_get_array_element(a_type_tail);
         b_type_tail = glsl_get_array_element(b_type_tail);
      }
      if (glsl_type_is_array(b_type_tail))
         return false;
   } else {
      a_type_tail = glsl_without_array(a_type_tail);
      b_type_tail = glsl_without_array(b_type_tail);
   }

   if (!glsl_type_is_vector_or_scalar(a_type_tail) ||
       !glsl_type_is_vector_or_scalar(b_type_tail))
      return false;

   if (glsl_get_base_type(a_type_tail) != glsl_get_base_type(b_type_tail))
      return false;

   assert(a->data.mode == b->data.mode);
   if (shader->info.stage == MESA_SHADER_FRAGMENT &&
       a->data.mode == nir_var_shader_in &&
       a->data.interpolation != b->data.interpolation)
      return false;

   return true;
}

static const struct glsl_type *
get_flat_type(nir_shader *shader, nir_variable *old_vars[MAX_SLOTS][4],
              unsigned *loc, nir_variable **first_var)
{
   unsigned todo = 1;
   unsigned slots = 0;
   *first_var = NULL;

   while (todo) {
      assert(*loc < MAX_SLOTS);
      for (unsigned frac = 0; frac < 4; frac++) {
         nir_variable *var = old_vars[*loc][frac];
         if (!var)
            continue;
         if ((*first_var && !variables_can_merge(shader, var, *first_var, false)) ||
             var->data.compact) {
            (*loc)++;
            return NULL;
         }

         if (!*first_var)
            *first_var = var;

         bool vs_in = shader->info.stage == MESA_SHADER_VERTEX &&
                      var->data.mode == nir_var_shader_in;
         unsigned slots = glsl_count_attribute_slots(var->type, vs_in);
         todo = MAX2(todo, slots);
      }
      todo--;
      slots++;
      if (todo)
         (*loc)++;
   }

   if (!*first_var)
      return NULL;

   enum glsl_base_type base = glsl_get_base_type(glsl_without_array((*first_var)->type));
   return glsl_array_type(glsl_vector_type(base, 4), slots, 0);
}

static bool
create_new_io_vars(nir_shader *shader, struct exec_list *io_list,
                   nir_variable *old_vars[MAX_SLOTS][4],
                   nir_variable *new_vars[MAX_SLOTS][4],
                   bool flat_vars[MAX_SLOTS])
{
   if (exec_list_is_empty(io_list))
      return false;

   nir_foreach_variable(var, io_list) {
      if (variable_can_rewrite(var)) {
         unsigned loc = var->data.location;
         unsigned frac = var->data.location_frac;
         old_vars[loc][frac] = var;
      }
   }

   bool merged_any_vars = false;

   for (unsigned loc = 0; loc < MAX_SLOTS; loc++) {
      nir_variable *first_var;
      unsigned new_loc = loc;
      const struct glsl_type *flat_type = get_flat_type(shader, old_vars, &new_loc, &first_var);
      if (flat_type) {
         merged_any_vars = true;

         nir_variable *var = nir_variable_clone(first_var, shader);
         var->data.location_frac = 0;
         var->type = flat_type;

         nir_shader_add_variable(shader, var);
         for (unsigned i = 0; i < glsl_get_length(flat_type); i++) {
            for (unsigned j = 0; j < 4; j++)
               new_vars[loc + i][j] = var;
            flat_vars[loc + i] = true;
         }
      }
      loc = new_loc;
   }

   for (unsigned loc = 0; loc < MAX_SLOTS; loc++) {
      if (flat_vars[loc])
         continue;

      unsigned frac = 0;
      while (frac < 4) {
         nir_variable *first_var = old_vars[loc][frac];
         if (!first_var) {
            frac++;
            continue;
         }

         int first = frac;
         bool found_merge = false;

         while (frac < 4) {
            nir_variable *var = old_vars[loc][frac];
            if (!var)
               break;

            if (var != first_var) {
               if (!variables_can_merge(shader, first_var, var, true))
                  break;

               found_merge = true;
            }

            const unsigned num_components =
               glsl_get_components(glsl_without_array(var->type));

            /* We had better not have any overlapping vars */
            for (unsigned i = 1; i < num_components; i++)
               assert(old_vars[loc][frac + i] == NULL);

            frac += num_components;
         }

         if (!found_merge)
            continue;

         merged_any_vars = true;

         nir_variable *var = nir_variable_clone(old_vars[loc][first], shader);
         var->data.location_frac = first;
         var->type = resize_array_vec_type(var->type, frac - first);

         nir_shader_add_variable(shader, var);
         for (unsigned i = first; i < frac; i++)
            new_vars[loc][i] = var;
      }
   }

   return merged_any_vars;
}

static nir_deref_instr *
build_array_deref_of_new_var(nir_builder *b, nir_variable *new_var,
                             nir_deref_instr *leader)
{
   if (leader->deref_type == nir_deref_type_var)
      return nir_build_deref_var(b, new_var);

   nir_deref_instr *parent =
      build_array_deref_of_new_var(b, new_var, nir_deref_instr_parent(leader));

   return nir_build_deref_follower(b, parent, leader);
}

static nir_ssa_def *
build_array_index(nir_builder *b, nir_deref_instr *deref, nir_ssa_def *base,
                  bool vs_in)
{
   switch (deref->deref_type) {
   case nir_deref_type_var:
      return base;
   case nir_deref_type_array: {
      nir_ssa_def *index = nir_i2i(b, deref->arr.index.ssa,
                                   deref->dest.ssa.bit_size);
      return nir_iadd(b, build_array_index(b, nir_deref_instr_parent(deref), base, vs_in),
                      nir_imul_imm(b, index, glsl_count_attribute_slots(deref->type, vs_in)));
   }
   default:
      unreachable("Invalid deref instruction type");
   }
}

static nir_deref_instr *
build_array_deref_of_new_var_flat(nir_shader *shader,
                                  nir_builder *b, nir_variable *new_var,
                                  nir_deref_instr *leader, unsigned base)
{
   bool vs_in = shader->info.stage == MESA_SHADER_VERTEX &&
                new_var->data.mode == nir_var_shader_in;
   return nir_build_deref_array(b, nir_build_deref_var(b, new_var),
                                build_array_index(b, leader, nir_imm_int(b, base), vs_in));
}

static bool
nir_lower_io_to_vector_impl(nir_function_impl *impl, nir_variable_mode modes)
{
   assert(!(modes & ~(nir_var_shader_in | nir_var_shader_out)));

   nir_builder b;
   nir_builder_init(&b, impl);

   nir_metadata_require(impl, nir_metadata_dominance);

   nir_shader *shader = impl->function->shader;
   nir_variable *old_inputs[MAX_SLOTS][4] = {{0}};
   nir_variable *new_inputs[MAX_SLOTS][4] = {{0}};
   nir_variable *old_outputs[MAX_SLOTS][4] = {{0}};
   nir_variable *new_outputs[MAX_SLOTS][4] = {{0}};
   bool flat_inputs[MAX_SLOTS] = {0};
   bool flat_outputs[MAX_SLOTS] = {0};

   if (modes & nir_var_shader_in) {
      /* Vertex shaders support overlapping inputs.  We don't do those */
      assert(b.shader->info.stage != MESA_SHADER_VERTEX);

      /* If we don't actually merge any variables, remove that bit from modes
       * so we don't bother doing extra non-work.
       */
      if (!create_new_io_vars(shader, &shader->inputs,
                              old_inputs, new_inputs,
                              flat_inputs))
         modes &= ~nir_var_shader_in;
   }

   if (modes & nir_var_shader_out) {
      /* If we don't actually merge any variables, remove that bit from modes
       * so we don't bother doing extra non-work.
       */
      if (!create_new_io_vars(shader, &shader->outputs,
                              old_outputs, new_outputs,
                              flat_outputs))
         modes &= ~nir_var_shader_out;
   }

   if (!modes)
      return false;

   bool progress = false;

   /* Actually lower all the IO load/store intrinsics.  Load instructions are
    * lowered to a vector load and an ALU instruction to grab the channels we
    * want.  Outputs are lowered to a write-masked store of the vector output.
    * For non-TCS outputs, we then run nir_lower_io_to_temporaries at the end
    * to clean up the partial writes.
    */
   nir_foreach_block(block, impl) {
      nir_foreach_instr_safe(instr, block) {
         if (instr->type != nir_instr_type_intrinsic)
            continue;

         nir_intrinsic_instr *intrin = nir_instr_as_intrinsic(instr);

         switch (intrin->intrinsic) {
         case nir_intrinsic_load_deref:
         case nir_intrinsic_interp_deref_at_centroid:
         case nir_intrinsic_interp_deref_at_sample:
         case nir_intrinsic_interp_deref_at_offset: {
            nir_deref_instr *old_deref = nir_src_as_deref(intrin->src[0]);
            if (!(old_deref->mode & modes))
               break;

            if (old_deref->mode == nir_var_shader_out)
               assert(b.shader->info.stage == MESA_SHADER_TESS_CTRL ||
                      b.shader->info.stage == MESA_SHADER_FRAGMENT);

            nir_variable *old_var = nir_deref_instr_get_variable(old_deref);

            const unsigned loc = old_var->data.location;
            const unsigned old_frac = old_var->data.location_frac;
            nir_variable *new_var = old_deref->mode == nir_var_shader_in ?
                                    new_inputs[loc][old_frac] :
                                    new_outputs[loc][old_frac];
            bool flat = old_deref->mode == nir_var_shader_in ?
                        flat_inputs[loc] : flat_outputs[loc];
            if (!new_var)
               break;

            const unsigned new_frac = new_var->data.location_frac;

            nir_component_mask_t vec4_comp_mask =
               ((1 << intrin->num_components) - 1) << old_frac;

            b.cursor = nir_before_instr(&intrin->instr);

            /* Rewrite the load to use the new variable and only select a
             * portion of the result.
             */
            nir_deref_instr *new_deref;
            if (flat) {
               new_deref = build_array_deref_of_new_var_flat(
                  shader, &b, new_var, old_deref, loc - new_var->data.location);
            } else {
               assert(new_var->data.location == loc);
               new_deref = build_array_deref_of_new_var(&b, new_var, old_deref);
               assert(glsl_type_is_vector(new_deref->type));
            }
            nir_instr_rewrite_src(&intrin->instr, &intrin->src[0],
                                  nir_src_for_ssa(&new_deref->dest.ssa));

            intrin->num_components =
               glsl_get_components(new_deref->type);
            intrin->dest.ssa.num_components = intrin->num_components;

            b.cursor = nir_after_instr(&intrin->instr);

            nir_ssa_def *new_vec = nir_channels(&b, &intrin->dest.ssa,
                                                vec4_comp_mask >> new_frac);
            nir_ssa_def_rewrite_uses_after(&intrin->dest.ssa,
                                           nir_src_for_ssa(new_vec),
                                           new_vec->parent_instr);

            progress = true;
            break;
         }

         case nir_intrinsic_store_deref: {
            nir_deref_instr *old_deref = nir_src_as_deref(intrin->src[0]);
            if (old_deref->mode != nir_var_shader_out)
               break;

            nir_variable *old_var = nir_deref_instr_get_variable(old_deref);

            const unsigned loc = old_var->data.location;
            const unsigned old_frac = old_var->data.location_frac;
            nir_variable *new_var = new_outputs[loc][old_frac];
            bool flat = flat_outputs[loc];
            if (!new_var)
               break;

            const unsigned new_frac = new_var->data.location_frac;

            b.cursor = nir_before_instr(&intrin->instr);

            /* Rewrite the store to be a masked store to the new variable */
            nir_deref_instr *new_deref;
            if (flat) {
               new_deref = build_array_deref_of_new_var_flat(
                  shader, &b, new_var, old_deref, loc - new_var->data.location);
            } else {
               assert(new_var->data.location == loc);
               new_deref = build_array_deref_of_new_var(&b, new_var, old_deref);
               assert(glsl_type_is_vector(new_deref->type));
            }
            nir_instr_rewrite_src(&intrin->instr, &intrin->src[0],
                                  nir_src_for_ssa(&new_deref->dest.ssa));

            intrin->num_components =
               glsl_get_components(new_deref->type);

            nir_component_mask_t old_wrmask = nir_intrinsic_write_mask(intrin);

            assert(intrin->src[1].is_ssa);
            nir_ssa_def *old_value = intrin->src[1].ssa;
            nir_ssa_def *comps[4];
            for (unsigned c = 0; c < intrin->num_components; c++) {
               if (new_frac + c >= old_frac &&
                   (old_wrmask & 1 << (new_frac + c - old_frac))) {
                  comps[c] = nir_channel(&b, old_value,
                                         new_frac + c - old_frac);
               } else {
                  comps[c] = nir_ssa_undef(&b, old_value->num_components,
                                               old_value->bit_size);
               }
            }
            nir_ssa_def *new_value = nir_vec(&b, comps, intrin->num_components);
            nir_instr_rewrite_src(&intrin->instr, &intrin->src[1],
                                  nir_src_for_ssa(new_value));

            nir_intrinsic_set_write_mask(intrin,
                                         old_wrmask << (old_frac - new_frac));

            progress = true;
            break;
         }

         default:
            break;
         }
      }
   }

   if (progress) {
      nir_metadata_preserve(impl, nir_metadata_block_index |
                                  nir_metadata_dominance);
   }

   return progress;
}

bool
nir_lower_io_to_vector(nir_shader *shader, nir_variable_mode modes)
{
   bool progress = false;

   nir_foreach_function(function, shader) {
      if (function->impl)
         progress |= nir_lower_io_to_vector_impl(function->impl, modes);
   }

   return progress;
}
