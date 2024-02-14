..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_compressed_decoder_ports:

.. list-table:: compressed_decoder module IO ports
   :header-rows: 1

   * - Signal
     - IO
     - Connection
     - Type
     - Description

   * - ``instr_i``
     - in
     - FRONTEND
     - Input instruction which can be compressed
     - logic[31:0]

   * - ``instr_o``
     - out
     - ID_STAGE
     - Output instruction which is uncompressed
     - logic[31:0]

   * - ``illegal_instr_o``
     - out
     - TO_BE_COMPLETED
     - Illegal instruction exception
     - logic

   * - ``is_compressed_o``
     - out
     - TO_BE_COMPLETED
     - report if instruction is compressed
     - logic
