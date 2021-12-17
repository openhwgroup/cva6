..
   Copyright (c) 2020, 2021 OpenHW Group

   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

   https://solderpad.org/licenses/

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

.. _corev_dv:

COREV-DV
========

COREV-DV is the name given to a library of extensions to the Google `riscv-dv <https://github.com/google/riscv-dv>`_ instructuion stream generator.
Riscv-dv is implemented as a collection SystemVerilog classes extending from
`uvm_object <https://verificationacademy.com/verification-methodology-reference/uvm/docs_1.1d/html/files/base/uvm_object-svh.html>`_,
so extending riscv-dv classes to modify its behavior is straightforward.
For those cases where a specific instruction stream is required, it is implemented as an extension of an existing riscv-dv class.
Thus, riscv-dv is not modified allowing core-v-verif to easily take advantage of updates to the Google project.

Note that for the most part, core-v-verif uses riscv-dv "as is" and each core that is verified in core-v-verif is free to use whatever version of riscv-dv that suits the core's needs:

- riscv-dv "as is".
- corev-dv (extensions at $CORE_V_VERIF/lib/corev-dv
- core-specific extensions at $CORE_V_VERIF/$COREV_CORE)/env/corev-dv

A non-core-specific version of corev-dv resides at $CORE_V_VERIF/lib/corev-dv.
Here you will find a set of extensions to riscv-dv that are intended to be common across all (or at least most) CORE-V cores.

Using COREV-DV
--------------

When a Make target requires it, a specific hash of riscv-dv is cloned to $CORE_V_VERIF/$COREV_CORE/vendor_lib/riscv-dv.
The compile Makefiles will compile in the required extensions to generate the core-specific version of corev-dv needed for a test.
The `README <https://github.com/openhwgroup/core-v-verif/tree/master/mk/uvmt#corev-dv-generated-tests>`_ at $CORE_V_VERIF/mk/uvmt provides instructions for building and running a corev-dv generated test-program.

Extending COREV-DV
-------------------

It is to be expected that each unique core will require multiple extensions to riscv-dv.
These should be placed in $CORE_V_VERIF/$COREV_CORE/env/corev-dv.

For example $CORE_V_VERIF/lib/corev-dv/corev_asm_program_gen.sv implements an override of `riscv_gen_program_header::gen_program_header()` to enforce the use of common symbols required by the board support package.
Since each core's verification environment is likely to use a core-specific BSP, it is expected that each core will need to implement core-specific extensions to corev_asm_program_gen.sv.

Below is simplifed view of the core-v-verif directory tree showing the locations of riscv-dv and the base corev-dv extensions plus an example of core-specific extensions for the CV32E40P.

..
 $(CORE_V_VERIF)
    ├── docs
    ├── ...
    ├── lib
    │   ├── uvm_agents
    │   ├── ...
    │   └── corev-dv                            // core-v-verif extensions of riscv-dv classes
    │       ├── corev_asm_program_gen.sv        // extends riscv_asm_program_gen
    │       ├── ...
    │       └── instr_lib                       // core-v-verif extensions of riscv-dv instrunction streams
    └── cv32e40p
        ├── ...
        ├── env
        │   ├── corev-dv                        // cv32e40p-specific extensions of corev-dv classes
        │   │   ├── README.md
        │   │   ├── cv32e40p_asm_program_gen.sv // cv32e40p-specific extension of corev_asm_program_gen
        │   │   ├── ...
        │   │   ├── instr_lib                   // cv32e40p-specific extensions of corev instruction streams
        │   │   └── target
        │   └── uvme
        └── vendor_lib
                └── riscv-dv                    // riscv-dv (https://github.com/google/riscv-dv) is cloned to here

