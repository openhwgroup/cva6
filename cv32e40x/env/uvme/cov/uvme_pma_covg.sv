///////////////////////////////////////////////////////////////////////////////
// Copyright 2020 OpenHW Group
// Copyright 2020 BTA Design Services
// Copyright 2020 Silicon Labs, Inc.
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
//
///////////////////////////////////////////////////////////////////////////////

`uvm_analysis_imp_decl(_rvfi_pma)

/*
* Covergroups
*/
covergroup cg_pma_cfg(string name)
with function sample(uvma_core_cntrl_pma_region_c pma_region, bit is_ifetch, bit rw);
    option.name = name;
    `per_instance_fcov

    cp_main       : coverpoint(pma_region.main) {
        bins IO   = {0};
        bins MAIN = {1};
    }
    cp_bufferable : coverpoint(pma_region.bufferable) {
        bins NONBUF = {0};
        bins BUF    = {1};
    }
    cp_cacheable  : coverpoint(pma_region.cacheable) {
        bins NONCACHE = {0};
        bins CACHE    = {1};
    }
    cp_atomic     : coverpoint(pma_region.atomic) {
        bins NONATOMIC = {0};
        bins ATOMIC    = {1};
    }
    cp_ifetch     : coverpoint(is_ifetch) {
        bins DATA  = {0};
        bins INSTR = {1};
    }
    cp_rw         : coverpoint(rw) {
        bins WRITE = {0};
        bins READ  = {1};
    }

    cp_attr : cross cp_main, cp_bufferable, cp_cacheable, cp_atomic, cp_ifetch, cp_rw {
       ignore_bins INSTR_WRITE = binsof(cp_ifetch) intersect {1} &&
                                 binsof(cp_rw) intersect {0};
    }

endgroup : cg_pma_cfg

class uvme_pma_covg extends uvm_component;

   /*
   * Class members
   */
   uvma_core_cntrl_cfg_c cfg;

   cg_pma_cfg   pma0_cfg_cg;
   cg_pma_cfg   pma1_cfg_cg;
   cg_pma_cfg   pma2_cfg_cg;
   cg_pma_cfg   pma3_cfg_cg;
   cg_pma_cfg   pma4_cfg_cg;
   cg_pma_cfg   pma5_cfg_cg;
   cg_pma_cfg   pma6_cfg_cg;
   cg_pma_cfg   pma7_cfg_cg;
   cg_pma_cfg   pma8_cfg_cg;
   cg_pma_cfg   pma9_cfg_cg;
   cg_pma_cfg   pma10_cfg_cg;
   cg_pma_cfg   pma11_cfg_cg;
   cg_pma_cfg   pma12_cfg_cg;
   cg_pma_cfg   pma13_cfg_cg;
   cg_pma_cfg   pma14_cfg_cg;
   cg_pma_cfg   pma15_cfg_cg;

   uvm_analysis_imp_rvfi_pma#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvme_pma_covg) rvfi_pma_export;

   `uvm_component_utils(uvme_pma_covg);

   extern function new(string name = "pma_covg", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern task run_phase(uvm_phase phase);

   extern function void write_rvfi_pma(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);

   extern function void sample_pma(int unsigned region_index, bit is_ifetch, bit is_read);

endclass : uvme_pma_covg

function uvme_pma_covg::new(string name = "pma_covg", uvm_component parent = null);

   super.new(name, parent);

   rvfi_pma_export = new("rvfi_pma_export", this);

endfunction : new

function void uvme_pma_covg::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   if (0 < cfg.pma_regions.size()) pma0_cfg_cg = new("pma0_cfg_cg");
   if (1 < cfg.pma_regions.size()) pma1_cfg_cg = new("pma1_cfg_cg");
   if (2 < cfg.pma_regions.size()) pma2_cfg_cg = new("pma2_cfg_cg");
   if (3 < cfg.pma_regions.size()) pma3_cfg_cg = new("pma3_cfg_cg");
   if (4 < cfg.pma_regions.size()) pma4_cfg_cg = new("pma4_cfg_cg");
   if (5 < cfg.pma_regions.size()) pma5_cfg_cg = new("pma5_cfg_cg");
   if (6 < cfg.pma_regions.size()) pma6_cfg_cg = new("pma6_cfg_cg");
   if (7 < cfg.pma_regions.size()) pma7_cfg_cg = new("pma7_cfg_cg");
   if (8 < cfg.pma_regions.size()) pma8_cfg_cg = new("pma8_cfg_cg");
   if (9 < cfg.pma_regions.size()) pma9_cfg_cg = new("pma9_cfg_cg");
   if (10 < cfg.pma_regions.size()) pma10_cfg_cg = new("pma10_cfg_cg");
   if (11 < cfg.pma_regions.size()) pma11_cfg_cg = new("pma11_cfg_cg");
   if (12 < cfg.pma_regions.size()) pma12_cfg_cg = new("pma12_cfg_cg");
   if (13 < cfg.pma_regions.size()) pma13_cfg_cg = new("pma13_cfg_cg");
   if (14 < cfg.pma_regions.size()) pma14_cfg_cg = new("pma14_cfg_cg");
   if (15 < cfg.pma_regions.size()) pma15_cfg_cg = new("pma15_cfg_cg");

endfunction : build_phase

task uvme_pma_covg::run_phase(uvm_phase phase);

   super.run_phase(phase);

   `uvm_info("PMACOVG", "The PMA coverage model is running", UVM_LOW);

endtask : run_phase

function void uvme_pma_covg::sample_pma(int unsigned region_index, bit is_ifetch, bit is_read);

   if (0  == region_index) pma0_cfg_cg.sample(cfg.pma_regions[0], is_ifetch, is_read);
   if (1  == region_index) pma1_cfg_cg.sample(cfg.pma_regions[1], is_ifetch, is_read);
   if (2  == region_index) pma2_cfg_cg.sample(cfg.pma_regions[2], is_ifetch, is_read);
   if (3  == region_index) pma3_cfg_cg.sample(cfg.pma_regions[3], is_ifetch, is_read);
   if (4  == region_index) pma4_cfg_cg.sample(cfg.pma_regions[4], is_ifetch, is_read);
   if (5  == region_index) pma5_cfg_cg.sample(cfg.pma_regions[5], is_ifetch, is_read);
   if (6  == region_index) pma6_cfg_cg.sample(cfg.pma_regions[6], is_ifetch, is_read);
   if (7  == region_index) pma7_cfg_cg.sample(cfg.pma_regions[7], is_ifetch, is_read);
   if (8  == region_index) pma8_cfg_cg.sample(cfg.pma_regions[8], is_ifetch, is_read);
   if (9  == region_index) pma9_cfg_cg.sample(cfg.pma_regions[9], is_ifetch, is_read);
   if (10 == region_index) pma10_cfg_cg.sample(cfg.pma_regions[10], is_ifetch, is_read);
   if (11 == region_index) pma11_cfg_cg.sample(cfg.pma_regions[11], is_ifetch, is_read);
   if (12 == region_index) pma12_cfg_cg.sample(cfg.pma_regions[12], is_ifetch, is_read);
   if (13 == region_index) pma13_cfg_cg.sample(cfg.pma_regions[13], is_ifetch, is_read);
   if (14 == region_index) pma14_cfg_cg.sample(cfg.pma_regions[14], is_ifetch, is_read);
   if (15 == region_index) pma15_cfg_cg.sample(cfg.pma_regions[15], is_ifetch, is_read);

endfunction : sample_pma

function void uvme_pma_covg::write_rvfi_pma(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);

    for (int i = 0; i < cfg.pma_regions.size(); i++) begin
        if (cfg.pma_regions[i].is_addr_in_region(trn.pc_rdata)) begin
            sample_pma(i, .is_ifetch(1), .is_read(1));
        end
    end

endfunction : write_rvfi_pma
