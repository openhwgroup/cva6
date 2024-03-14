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


Compressed_decoder
~~~~~~~~~~~~~~~~~~

The compressed_decoder module decompresses all the compressed
instructions taking a 16-bit compressed instruction and expanding it
to its 32-bit equivalent.
All compressed instructions have a 32-bit equivalent.

.. include:: port_compressed_decoder.rst

Decoder
~~~~~~~

The decoder module takes the output of compressed_decoder module and decodes it.
It transforms the instruction to the most fundamental control structure in pipeline, a scoreboard entry.

The scoreboard entry contains an exception entry which is composed of a valid field, a cause and a value called TVAL.
As TVALEn configuration parameter is zero, the TVAL field is not implemented.

A potential illegal instruction exception can be detected during decoding.
If no exception has happened previously in fetch stage, the decoder will valid the exception and add the cause and tval value to the scoreboard entry.

.. include:: port_decoder.rst

