..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales DIS design services SAS

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_custom_instructions:

*This chapter is applicable to all configurations.*

Custom RISC-V instructions
==========================
As of now, CVA6 does not implement custom RISC-V instructions.

The team is looking for contributors to implement the ``fence.t`` instruction that ensures that the execution time of subsequent instructions is unrelated with predecessor instructions.

The user or integrator can also use the CV-X-IF coprocessor interface to implement their own extensions, without modifying the core.
