// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

/**** AXI interface to indicate the state of the agent ****/


interface uvmt_default_inputs_intf;

   logic [63:0] hart_id;
   logic [1:0]  irq;
   logic        ipi;
   logic        time_irq;
   logic        debug_req;

endinterface : uvmt_default_inputs_intf
