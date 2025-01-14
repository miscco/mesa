
template = """\
/* 
 * Copyright (c) 2018 Valve Corporation
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

#include "aco_ir.h"

namespace aco {

const unsigned VOPC_to_GFX6[256] = {
% for code in VOPC_GFX6:
    ${code},
% endfor
};

<%
opcode_names = sorted(opcodes.keys())
can_use_input_modifiers = "".join([opcodes[name].input_mod for name in reversed(opcode_names)])
can_use_output_modifiers = "".join([opcodes[name].output_mod for name in reversed(opcode_names)])
%>

extern const aco::Info instr_info = {
   .opcode_gfx9 = {
      % for name in opcode_names:
      ${opcodes[name].opcode_gfx9},
      % endfor
   },
   .can_use_input_modifiers = std::bitset<${len(opcode_names)}>("${can_use_input_modifiers}"),
   .can_use_output_modifiers = std::bitset<${len(opcode_names)}>("${can_use_output_modifiers}"),
   .name = {
      % for name in opcode_names:
      "${name}",
      % endfor
   },
   .format = {
      % for name in opcode_names:
      aco::Format::${str(opcodes[name].format.name)},
      % endfor
   },
};

}
"""

from aco_opcodes import opcodes, VOPC_GFX6
from mako.template import Template

print(Template(template).render(opcodes=opcodes, VOPC_GFX6=VOPC_GFX6))
