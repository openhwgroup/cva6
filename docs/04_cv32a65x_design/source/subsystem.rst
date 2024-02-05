..
   Copyright 2022 Thales DIS design services SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales



Subsystem
=========

Global functionality
--------------------

The CVA6 is a subsystem composed of the modules and protocol interfaces as illustrated 
The processor is a Harvard-based modern architecture.
Instructions are issued in-order through the DECODE stage and executed out-of-order but committed in-order.
The processor is Single issue, that means that at maximum one instruction per cycle can be issued to the EXECUTE stage.

The CVA6 implements a 6-stage pipeline composed of PC Generation, Instruction Fetch, Instruction Decode, Issue stage, Execute stage and Commit stage.
At least 6 cycles are needed to execute one instruction.

Connection with other sub-systems
---------------------------------

[TO BE COMPLETED]


Parameter list
--------------

[TO BE COMPLETED]


Parameter configuration
-----------------------

.. list-table:: Risc-V Configuration
   :header-rows: 1

   * - Standard Extension
     - Specification
     - Configurability

   * - **I**: RV32i Base Integer Instruction Set
     - [RVunpriv]
     - ON

   * - **C**: Standard Extension for Compressed Instructions
     - [RVunpriv]
     - ON

   * - **M**: Standard Extension for Integer Multiplication and Division
     - [RVunpriv]
     - ON

   * - **A**: Standard Extension for Atomic transaction
     - [RVunpriv]
     - OFF

   * - **F and D**: Single and Double Precision Floating-Point
     - [RVunpriv]
     - OFF

   * - **Zicount**: Performance Counters
     - [RVunpriv]
     - OFF

   * - **Zicsr**: Control and Status Register Instructions
     - [RVpriv]
     - ON

   * - **Zifencei**: Instruction-Fetch Fence
     - [RVunpriv]
     - ON

   * - **Privilege**: Standard privilege modes M, S and U
     - [RVpriv]
     - ON

   * - **SV39, SV32, SV0**: MMU capability
     - [RVpriv]
     - OFF

   * - **PMP**: Memory Protection Unit
     - [RVpriv]
     - OFF

   * - **CSR**: Control and Status Registers
     - [RVpriv]
     - ON

   * - **AXI**: AXI interface
     - [CV-X-IF]
     - ON

   * - **TRI**: Translation Response Interface (TRI)
     - [OpenPiton]
     - OFF


.. list-table:: Micro-Architecture Configuration
   :header-rows: 1

   * - Micro-architecture
     - Specification
     - Configurability

   * - **I$**: Instruction cache
     - current spec
     - ON

   * - **D$**: Data cache
     - current spec
     - OFF

   * - **Rename**: register Renaming
     - current spec
     - OFF

   * - **Double Commit**: out of order pipeline execute stage
     - current spec
     - ON

   * - **BP**: Branch Prediction
     - current spec
     - ON with no info storage


IO ports
--------

.. include:: port_cva6.rst
