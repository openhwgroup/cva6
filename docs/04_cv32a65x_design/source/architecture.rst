..
   Copyright 2022 Thales DIS design services SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales



Architecture and Modules
========================

The CV32A65X is fully synthesizable. It has been designed mainly for ASIC designs, but FPGA synthesis is supported as well.

For ASIC synthesis, the whole design is completely synchronous and uses positive-edge triggered flip-flops. The core occupies an area of about 80 kGE. The clock frequency can be more than 1GHz depending of technology.

The CV32A65X subsystem is composed of 8 modules.

.. figure:: ../images/subsystems.png
   :name: CV32A6 v0.1.0 modules
   :align: center
   :alt:

   CV32A65X modules

Connections between modules are illustrated in the following block diagram. FRONTEND, DECODE, ISSUE, EXECUTE, COMMIT and CONTROLLER are part of the pipeline. And CACHES implements the instruction and data caches and CSRFILE contains registers.

.. figure:: ../images/CV32A65X_subsystems.png
   :name: CV32A65X subsystem
   :align: center
   :alt:

   CV32A65X pipeline and modules

.. toctree::
   :hidden:

   cv32a6_frontend
   cva6_id_stage
   cva6_issue_stage
   cv32a6_execute
   cva6_commit_stage
   cva6_controller
   cva6_csr_regfile
   cva6_caches
