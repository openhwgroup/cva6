// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2021 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_SB_SV__
`define __UVME_CVA6_SB_SV__


/**
 * Component encapsulating scoreboards which compare CVA6
 * DUT's expected (from predictor) vs. actual (monitored) transactions.
 */
class uvme_cva6_sb_c extends uvm_scoreboard;

   // Objects
   uvme_cva6_cfg_c    cfg;
   uvme_cva6_cntxt_c  cntxt;

   // Components
   // TODO Add sub-scoreboards
   //      Ex: uvme_cva6_sb_simplex_c  egress_sb;
   //          uvme_cva6_sb_simplex_c  ingress_sb;
   uvmc_rvfi_scoreboard_c#(ILEN,XLEN) m_rvfi_scoreboard;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_isacov_mon_trn_c)  instr_trn_fifo;

   uvma_isacov_mon_trn_c instr_trn;

   // Store previous instruction
   uvma_isacov_instr_c instr_prev;

   // Store MTVEC value
   bit [XLEN-1:0]  mtvec_value = 'h0;

   // Store MEPC value
   bit [XLEN-1:0]  mepc_value;

   // Store trap pc value
   bit [XLEN-1:0]  trap_pc;

   // Flag to see if mtvec/mepc has been changed
   bit  mtvec_change = 'h0;
   bit  mepc_change = 'h0;
   static bit  has_trap = 0;

   // Flag for compressed instruction
   bit trap_is_compressed;

   `uvm_component_utils_begin(uvme_cva6_sb_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)

      // TODO Add sub-scoreboards field macros
      //      Ex: `uvm_field_object(egress_sb , UVM_DEFAULT)
      //          `uvm_field_object(ingress_sb, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cva6_sb", uvm_component parent=null);

   /**
    * Create and configures sub-scoreboards via:
    * 1. assign_cfg()
    * 2. assign_cntxt()
    * 3. create_sbs()
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Assigns configuration handles.
    */
   extern virtual function void assign_cfg();

   /**
    * Assigns context handles.
    */
   extern virtual function void assign_cntxt();

   /**
    * Creates sub-scoreboard components.
    */
   extern virtual function void create_sbs();

   /**
    * Check after a trap the CVA6 jump to the value in mtvec
    */
   extern virtual function void check_pc_trap(uvma_isacov_instr_c instr, uvma_isacov_instr_c instr_prev);

   /**
    * Check after a trap mepc has the pc trap
    */
   extern virtual function void check_mepc(uvma_isacov_instr_c instr);

   /**
    * Creates sub-scoreboard components.
    */
   extern task run_phase(uvm_phase phase);

endclass : uvme_cva6_sb_c


function uvme_cva6_sb_c::new(string name="uvme_cva6_sb", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvme_cva6_sb_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvme_cva6_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   instr_trn_fifo   = new("instr_trn_fifo" , this);

   assign_cfg  ();
   assign_cntxt();
   create_sbs  ();

endfunction : build_phase


function void uvme_cva6_sb_c::assign_cfg();

   // TODO Implement uvme_cva6_sb_c::assign_cfg()
   //      Ex: uvm_config_db#(uvm_sb_cfg_c)::set(this, "egress_sb" , "cfg", cfg.sb_egress_cfg );
   //          uvm_config_db#(uvm_sb_cfg_c)::set(this, "ingress_sb", "cfg", cfg.sb_ingress_cfg);

endfunction : assign_cfg


function void uvme_cva6_sb_c::assign_cntxt();

   // TODO Implement uvme_cva6_sb_c::assign_cntxt()
   //      Ex: uvm_config_db#(uvme_cva6_sb_cntxt_c)::set(this, "egress_sb" , "cntxt", cntxt.sb_egress_cntxt );
   //          uvm_config_db#(uvme_cva6_sb_cntxt_c)::set(this, "ingress_sb", "cntxt", cntxt.sb_ingress_cntxt);

endfunction : assign_cntxt


function void uvme_cva6_sb_c::create_sbs();

   // TODO Implement uvme_cva6_sb_c::create_sbs()
   //      Ex: egress_sb  = uvme_cva6_sb_simplex_c::type_id::create("egress_sb" , this);
   //          ingress_sb = uvme_cva6_sb_simplex_c::type_id::create("ingress_sb", this);
    if (cfg.tandem_enabled)
        m_rvfi_scoreboard = uvmc_rvfi_scoreboard_c#(ILEN,XLEN)::type_id::create("m_rvfi_scoreboard", this);

endfunction : create_sbs

function void uvme_cva6_sb_c::check_pc_trap(uvma_isacov_instr_c instr,
                                            uvma_isacov_instr_c instr_prev);

  if (instr.group == uvma_isacov_pkg::CSR_GROUP && instr.is_csr_write() && instr.csr_val == 12'h305) begin
     if (instr.name == uvma_isacov_pkg::CSRRWI) begin
        mtvec_value = instr.rs1;
        mtvec_change = 1'h1;
        `uvm_info(get_type_name(), $sformatf("Write into MTVEC the value = 0x%h", mtvec_value), UVM_DEBUG)
     end
     if (instr.name == uvma_isacov_pkg::CSRRSI) begin
        mtvec_value = instr.rvfi.rd1_wdata | instr.rs1;
        mtvec_change = 1'h1;
        `uvm_info(get_type_name(), $sformatf("Write into MTVEC the value = 0x%h", mtvec_value), UVM_DEBUG)
     end
     if (instr.name == uvma_isacov_pkg::CSRRCI) begin
        mtvec_value = instr.rvfi.rd1_wdata & ~(instr.rs1);
        mtvec_change = 1'h1;
        `uvm_info(get_type_name(), $sformatf("Write into MTVEC the value = 0x%h", mtvec_value), UVM_DEBUG)
     end
     if (instr.name == uvma_isacov_pkg::CSRRW) begin
        mtvec_value = instr.rs1_value;
        mtvec_change = 1'h1;
        `uvm_info(get_type_name(), $sformatf("Write into MTVEC the value = 0x%h", mtvec_value), UVM_DEBUG)
     end
     if (instr.name == uvma_isacov_pkg::CSRRC) begin
        mtvec_value = instr.rvfi.rd1_wdata & ~(instr.rs1_value);
        mtvec_change = 1'h1;
        `uvm_info(get_type_name(), $sformatf("Write into MTVEC the value = 0x%h", mtvec_value), UVM_DEBUG)
     end
     if (instr.name == uvma_isacov_pkg::CSRRS) begin
        mtvec_value = instr.rvfi.rd1_wdata | instr.rs1_value;
        mtvec_change = 1'h1;
        `uvm_info(get_type_name(), $sformatf("Write into MTVEC the value = 0x%h", mtvec_value), UVM_DEBUG)
     end
  end

  if (instr_prev != null) begin
     if (instr_prev.trap) begin
        if (mtvec_change) begin
           if (instr.rvfi.pc_rdata[31:2] == mtvec_value[31:2]) begin
              //we only support MTVEC Direct mode
              `uvm_info(get_type_name(), $sformatf("After a trap, PC matches MTVEC value"), UVM_DEBUG)
           end
           else begin
              `uvm_fatal(get_type_name(), "ERROR -> Doesn't jump to MTVEC")
           end
        end
        else begin
             // TODO : need more checking on mtvec value
             `uvm_warning(get_type_name(), "BE CAREFUL -> MTVEC still has the reset value")
             return;
        end
     end
  end

endfunction : check_pc_trap

function void uvme_cva6_sb_c::check_mepc(uvma_isacov_instr_c instr);

  if (instr.trap) begin
     trap_pc = instr.rvfi.pc_rdata[31:0];
     `uvm_info(get_type_name(), $sformatf("Trap PC : 0x%h ", trap_pc), UVM_NONE)
     if (instr.rvfi.insn[1:0] == 2'h3) begin
        trap_is_compressed = 1'h0;
     end
     else begin
        trap_is_compressed = 1'h1;
     end
     if (trap_pc == instr.rvfi.name_csrs["mepc"].wdata) begin
         `uvm_info(get_type_name(), $sformatf("Trap PC has been written successfully "), UVM_DEBUG)
     end
     else begin
         `uvm_error(get_type_name(), "ERROR -> Trap PC != MEPC")
     end
     has_trap = 1'h1;
  end

  if (has_trap) begin
     if (instr.group == uvma_isacov_pkg::CSR_GROUP && instr.is_csr_write() && instr.csr_val == 12'h341) begin
        if (instr.name inside {uvma_isacov_pkg::CSRRWI, uvma_isacov_pkg::CSRRSI, uvma_isacov_pkg::CSRRCI}) begin
           mepc_value = instr.rs1;
           mepc_change = 1'h1;
           `uvm_info(get_type_name(), $sformatf("Write into MEPC the value = 0x%h", mepc_value), UVM_DEBUG)
        end
        else begin
           mepc_value = instr.rs1_value;
           mepc_change = 1'h1;
           `uvm_info(get_type_name(), $sformatf("Write into MEPC the value = 0x%h", mepc_value), UVM_DEBUG)
        end
     end

     if (instr.name == uvma_isacov_pkg::MRET) begin
         if (mepc_change) begin
            `uvm_info(get_type_name(), $sformatf("Trap is compressed ? : %h ", trap_is_compressed), UVM_DEBUG)
            if (trap_is_compressed) begin
               if (mepc_value != trap_pc + 'h2) begin
                  `uvm_warning(get_type_name(), $sformatf("BE CAREFUL -> MEPC hasn't the next instruction's PC 2"))
               end
            end
            else begin
               if (mepc_value != trap_pc + 'h4) begin
                  `uvm_warning(get_type_name(), $sformatf("BE CAREFUL -> MEPC hasn't the next instruction's PC 4"))
               end
            end
         end
         else begin
            `uvm_warning(get_type_name(), $sformatf("BE CAREFUL -> MEPC still has the trap pc, this could create an infinite loop "))
         end
     end
  end

endfunction : check_mepc

task uvme_cva6_sb_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

  forever begin
     instr_trn_fifo.get(instr_trn);
     check_pc_trap(instr_trn.instr, instr_prev);
     check_mepc(instr_trn.instr);
    // Move instructions down the pipeline
     instr_prev = instr_trn.instr;
  end

endtask : run_phase

`endif // __UVME_CVA6_SB_SV__
