..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_ID_STAGE:

ID_STAGE Module
===============

Description
-----------

The ID_STAGE module implements the decode stage of the pipeline.
Its main purpose is to decode RISC-V instructions coming from FRONTEND module
(fetch stage) and send them to the ISSUE_STAGE module (issue stage).

The compressed_decoder module checks whether the incoming instruction is
compressed and output the corresponding uncompressed instruction.
Then the decoder module decodes the instruction and send it to the
issue stage.


The module is connected to:

* CONTROLLER module can flush ID_STAGE decode stage
* FRONTEND module sends instrution to ID_STAGE module
* ISSUE module receives the decoded instruction from ID_STAGE module
* CSR_REGFILE module sends status information about privilege mode, traps, extension support.

.. include:: port_id_stage.rst



Functionality
-------------

TO BE COMPLETED


Submodules
----------

.. figure:: ../images/id_stage_modules.png
   :name: ID_STAGE submodules
   :align: center
   :alt:

   ID_STAGE submodules


Decoder
~~~~~~~

TO BE COMPLETED


Compressed_decoder
~~~~~~~~~~~~~~~~~~

TO BE COMPLETED

