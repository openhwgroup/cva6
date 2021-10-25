// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_CLKNRST_DRV_SV__
`define __UVMA_CLKNRST_DRV_SV__


/**
 * Component driving a Clock & Reset virtual interface (uvma_clknrst_if).
 */
class uvma_clknrst_drv_c extends uvm_driver#(
   .REQ(uvma_clknrst_seq_item_c),
   .RSP(uvma_clknrst_seq_item_c)
);
   
   // Objects
   uvma_clknrst_cfg_c    cfg;
   uvma_clknrst_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_clknrst_seq_item_c)  ap;
   
   
   `uvm_component_utils_begin(uvma_clknrst_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_clknrst_drv", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * Obtains the reqs from the sequence item port and calls drv_req()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_req(uvma_clknrst_seq_item_c req);
   
endclass : uvma_clknrst_drv_c


function uvma_clknrst_drv_c::new(string name="uvma_clknrst_drv", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_clknrst_drv_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_clknrst_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_clknrst_cfg_c)::set(this, "*", "cfg", cfg);
   
   void'(uvm_config_db#(uvma_clknrst_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_clknrst_cntxt_c)::set(this, "*", "cntxt", cntxt);
   
   ap = new("ap", this);
   
endfunction : build_phase


task uvma_clknrst_drv_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   case (cfg.drv_initial_rst_value)
      UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_1: cntxt.vif.reset_n = '1;
      UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_X: cntxt.vif.reset_n = 'X;
      
      default: begin
         `uvm_error("CLKNRST", $sformatf("Illegal cfg.initial_value: %s", cfg.drv_initial_rst_value))
      end
   endcase

   forever begin
      seq_item_port.get_next_item(req);
      `uvml_hrtbt()
      drv_req (req);
      ap.write(req);
      seq_item_port.item_done();
   end
   
endtask : run_phase


task uvma_clknrst_drv_c::drv_req(uvma_clknrst_seq_item_c req);
   
   case (req.action)
      UVMA_CLKNRST_SEQ_ITEM_ACTION_START_CLK: begin
         if (cntxt.vif.clk_active) begin
            `uvm_warning("CLKNRST", {"Attempting to start clock generation while it is already active. Ignoring req:\n", req.sprint()})
         end
         else begin
            if (req.clk_period != 0) begin
               cntxt.vif.set_period(req.clk_period * 1ps);
            end
            case (req.initial_value)
               UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_0: cntxt.vif.clk = '0;
               UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_1: cntxt.vif.clk = '1;
               UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_X: cntxt.vif.clk = 'X;
            endcase
            cntxt.vif.start_clk();
         end
      end
      
      UVMA_CLKNRST_SEQ_ITEM_ACTION_STOP_CLK: begin
         if (!cntxt.vif.clk_active) begin
            `uvm_warning("CLKNRST", {"Attempting to stop clock generation while it is already inactive. Ignoring req:\n", req.sprint()})
         end
         else begin
            wait (cntxt.vif.clk == 1'b0);
            cntxt.vif.stop_clk();
         end
      end

      UVMA_CLKNRST_SEQ_ITEM_ACTION_RESTART_CLK: begin
         if (cntxt.vif.clk_active) begin
            `uvm_warning("CLKNRST", {"Attempting to restart clock generation while it is already active. Ignoring req:\n", req.sprint()})
         end
         else begin
            cntxt.vif.start_clk();
         end
      end

      UVMA_CLKNRST_SEQ_ITEM_ACTION_ASSERT_RESET: begin
         `uvm_info("CLKNRST", $sformatf("Asserting reset for %0t", (req.rst_deassert_period * 1ps)), UVM_MEDIUM)
         cntxt.vif.reset_n = '0;
         #(req.rst_deassert_period * 1ps);
         `uvm_info("CLKNRST", "De-asserting reset", UVM_MEDIUM)
         cntxt.vif.reset_n = '1;
      end
   endcase
   
endtask : drv_req


`endif // __UVMA_CLKNRST_DRV_SV__
