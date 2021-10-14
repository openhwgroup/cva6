// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_SLV_R_MON_TRN_LOGGER_SV__
`define __UVMA_OBI_SLV_R_MON_TRN_LOGGER_SV__


/**
 * Component writing Open Bus Interface monitor transactions debug data to disk as plain text.
 */
class uvma_obi_slv_r_mon_trn_logger_c extends uvml_logs_mon_trn_logger_c#(
   .T_TRN  (uvma_obi_slv_r_mon_trn_c),
   .T_CFG  (uvma_obi_cfg_c          ),
   .T_CNTXT(uvma_obi_cntxt_c        )
);
   
   `uvm_component_utils(uvma_obi_slv_r_mon_trn_logger_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_slv_r_mon_trn_logger", uvm_component parent=null);
   
   /**
    * Writes contents of t to disk
    */
   extern virtual function void write(uvma_obi_slv_r_mon_trn_c t);
   
   /**
    * Writes log header to disk
    */
   extern virtual function void print_header();
   
endclass : uvma_obi_slv_r_mon_trn_logger_c


function uvma_obi_slv_r_mon_trn_logger_c::new(string name="uvma_obi_slv_r_mon_trn_logger", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_slv_r_mon_trn_logger_c::write(uvma_obi_slv_r_mon_trn_c t);
   
   // TODO Implement uvma_obi_slv_r_mon_trn_logger_c::write()
   // Ex: fwrite($sformatf(" %t | %08h | %02b | %04d | %02h |", $realtime(), t.a, t.b, t.c, t.d));
   
endfunction : write


function void uvma_obi_slv_r_mon_trn_logger_c::print_header();
   
   // TODO Implement uvma_obi_slv_r_mon_trn_logger_c::print_header()
   // Ex: fwrite("----------------------------------------------");
   //     fwrite(" TIME | FIELD A | FIELD B | FIELD C | FIELD D ");
   //     fwrite("----------------------------------------------");
   
endfunction : print_header


`endif // __UVMA_OBI_SLV_R_MON_TRN_LOGGER_SV__
