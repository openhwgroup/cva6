//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//


`ifndef __UVMT_CV32E40X_LDGEN_TB_SV__
`define __UVMT_CV32E40X_LDGEN_TB_SV__

`include "uvm_macros.svh"
`include "uvme_cv32e40x_macros.sv"

`include "cv32e40x_pkg.sv"
import cv32e40x_pkg::pma_region_t;
`include "uvmt_cv32e40x_constants.sv"
`include "pma_adapted_mem_region_gen.sv"
/**
 * provide UVM environment entry and exit points.
 */
`default_nettype none
module uvmt_cv32e40x_ldgen_tb;

   import uvm_pkg::*;
   import uvma_core_cntrl_pkg::*;

  /*
  *  LDGEN
  */

  // Output file names
  parameter string MEMORY_LAYOUT_FILE   = "linkcmds.memory";
  parameter string SECTIONS_PMA_FILE    = "linkcmds.pmasec";
  parameter string SECTIONS_DEBUG_FILE  = "linkcmds.dbgsec";
  parameter string FIXED_ADDR_FILE      = "linkcmds.fixadd";

  parameter PMA_NUM_REGIONS = CORE_PARAM_PMA_NUM_REGIONS ? CORE_PARAM_PMA_NUM_REGIONS : 2;

  // optionally create YAML configuration with OVPSIM overrides
  parameter CREATE_YAML_CFG           = 0;
  parameter CREATE_YAML_OVP_OVERRIDES = 0;

  // indentation level widths
  parameter L1                   = 3;
  parameter L2                   = 6;

  // Memory support - when enabled, the linker script gets code regions set to their
  // full extent specified by the PMA configuration - alternatively this can be disabled
  // to restrict memory regions to a certain size (4096*64 bytes per region default)
  parameter LARGE_MEMORY_SUPPORT = 1;
  parameter SMALL_MEM_LIMIT      = 'h40000;

  // Might be better to fetch this from common configuration object?
  // TODO: fetch and optionally modify DEBUG and any other hard coded regions to prevent
  // linker script conflicts.
  parameter RAM_ORIGIN           = 32'h0000_0000;
  parameter RAM_LENGTH           = 32'h40_0000;
  parameter BOOT_ADDR            = 32'h80;
  parameter NMI_ADDR             = 32'h30CAFE;
  parameter DEBUG_ORIGIN         = 32'h1A11_0800;
  parameter DEBUG_EXCEPTION_ADDR = 32'h1A11_1000;
  parameter DEBUG_STACK_OFFSET   = 32'h80;

  parameter DISABLE_DEFAULT_RAM_REGION = 1;
  parameter DISABLE_DEFAULT_DBG_REGION = 0;

  static string default_attributes = "(rwxai)";
  string nmi_memory_area;
  string region_attributes;
  string section_location;
  int region_length;
  int main_region = -1;
  bit disable_default_ram_region = !CORE_PARAM_PMA_NUM_REGIONS ? 0 : DISABLE_DEFAULT_RAM_REGION;
  bit disable_section_write = 0;
  int boot_region = -1;
  int nmi_region = -1;
  int fhandle_mem;
  int fhandle_pma;
  int fhandle_dbg;
  int fhandle_fix;
  int fhandle_yaml;

  pma_region_t regions[PMA_NUM_REGIONS][$];
  pma_region_t temp_region;
  int temp_region_ctr;
  pma_adapted_memory_regions_c pma_adapted_memory;
  uvme_cv32e40x_core_cntrl_if

  function string indent(int num_indent);
    string indent_val;
    indent_val.itoa(num_indent);
    return $sformatf( { "%-", indent_val , "s" } , " " );
  endfunction : indent

  initial begin : start_of_ldgen

    pma_adapted_memory = new(CORE_PARAM_PMA_CFG);
    pma_adapted_memory.check_regions;

    if (PMA_NUM_REGIONS == 0 && disable_default_ram_region) begin
      $fatal(1, "Wrong setting: No memory region available");
    end
    fhandle_mem = $fopen(MEMORY_LAYOUT_FILE,  "w");
    if (!fhandle_mem) begin
      $fatal(1, $sformatf("Unable to open %s", MEMORY_LAYOUT_FILE));
    end
    fhandle_pma = $fopen(SECTIONS_PMA_FILE,   "w");
    if (!fhandle_pma) begin
      $fatal(1, $sformatf("Unable to open %s", SECTIONS_PMA_FILE));
    end
    fhandle_dbg = $fopen(SECTIONS_DEBUG_FILE, "w");
    if (!fhandle_dbg) begin
      $fatal(1, $sformatf("Unable to open %s", SECTIONS_DEBUG_FILE));
    end
    fhandle_fix = $fopen(FIXED_ADDR_FILE, "w");
    if (!fhandle_fix) begin
      $fatal(1, $sformatf("Unable to open %s", FIXED_ADDR_FILE));
    end

    // ############################################################
    // Generate memory file
    // ############################################################
    $fdisplay(fhandle_mem, "MEMORY");
    $fdisplay(fhandle_mem, "{");

    // Optionally disable default ram region definition
    if (!disable_default_ram_region) begin
      $fdisplay(fhandle_mem, { indent(L1), $sformatf("ram (rwxai) : ORIGIN = 0x%08d, LENGTH = 0x%6d", RAM_ORIGIN, RAM_LENGTH) });
    end

    if (!DISABLE_DEFAULT_DBG_REGION) begin
      // Debug is not aliased to some other region, so we need to make sure this code is only in place if debug is enabled
      $fdisplay(fhandle_mem, { indent(L1), $sformatf("dbg (rwxai) : ORIGIN = 0x%08x, LENGTH = 0x1000", DEBUG_ORIGIN) });
    end

    if (CORE_PARAM_PMA_NUM_REGIONS > 0) begin
      foreach (pma_adapted_memory.region[i]) begin

        if (BOOT_ADDR inside { [pma_adapted_memory.region[i].cfg.word_addr_low : pma_adapted_memory.region[i].cfg.word_addr_high] }) begin
          if (pma_adapted_memory.region[i].cfg.main != 1) begin
            $fatal(1, $sformatf("Boot address is not in executable region!"));
          end
          main_region = i;
          disable_section_write = 1;
        end else begin
          `uvm_fatal("DEBUG", $sformatf("Boot address (0x%8x) is not in any region, regions not covered by PMA are not executable!", BOOT_ADDR));
        end
        if (NMI_ADDR inside  { [pma_adapted_memory.region[i].cfg.word_addr_low : pma_adapted_memory.region[i].cfg.word_addr_high] }) begin
          nmi_region = i;
        end

        if (!(pma_adapted_memory.region[i].cfg.main)) begin
          region_attributes = "(!i)";
        end else begin
          region_attributes = default_attributes;
        end

        // Allow large memory regions if enabled, otherwise restrict to max SMALL_MEM_LIMIT
        if (LARGE_MEMORY_SUPPORT) begin
          region_length = (pma_adapted_memory.region[i].cfg.word_addr_high << 2) - (pma_adapted_memory.region[i].cfg.word_addr_low << 2);
        end else begin
          if ((pma_adapted_memory.region[i].cfg.word_addr_high << 2) - (pma_adapted_memory.region[i].cfg.word_addr_low << 2) <= SMALL_MEM_LIMIT) begin
            region_length = (pma_adapted_memory.region[i].cfg.word_addr_high << 2) - (pma_adapted_memory.region[i].cfg.word_addr_low << 2);
          end else begin
            region_length = SMALL_MEM_LIMIT;
          end
        end

        // Write to memory.ld
        $fdisplay(fhandle_mem, { indent(L1), $sformatf("region_%-2d %-7s : ORIGIN = 0x%08x, LENGTH = 0x%08x",
                                                      i, region_attributes, pma_adapted_memory.region[i].cfg.word_addr_low<<2, region_length) });
      end
    end

    $fdisplay(fhandle_mem, "}");

    // if the default ram region is enabled, we alias the lowest numbered executable pma region to ram (boot address needs to be set accordingly)
    if (disable_default_ram_region) begin
      $fdisplay(fhandle_mem, { "REGION_ALIAS(\"ram\", region_", $sformatf("%0d", main_region), ");" });
    end

    $fclose(fhandle_mem);

    // ############################################################
    // Generate debug file
    // ############################################################

    // Conditionally create the contents of the debug.ld file, otherwise it will be overwritten with an empty file
    if (!DISABLE_DEFAULT_DBG_REGION) begin
      $fdisplay(fhandle_dbg, "SECTIONS");
      $fdisplay(fhandle_dbg, "{");
      $fdisplay(fhandle_dbg, { indent(L1), ".debugger (ORIGIN(dbg)):" });
      $fdisplay(fhandle_dbg, { indent(L1), "{" });
      $fdisplay(fhandle_dbg, { indent(L2), "KEEP(*(.debugger));" });
      $fdisplay(fhandle_dbg, { indent(L1), "} >dbg" });

      $fdisplay(fhandle_dbg, { indent(L1), ".debugger_exception ", $sformatf("(0x%8x):", DEBUG_EXCEPTION_ADDR) });
      $fdisplay(fhandle_dbg, { indent(L1), "{" });
      $fdisplay(fhandle_dbg, { indent(L2), "KEEP(*(.debugger_exception));" });
      $fdisplay(fhandle_dbg, { indent(L1), "} >dbg" });

      $fdisplay(fhandle_dbg, { indent(L1), ".debugger_stack : ALIGN(16)" });
      $fdisplay(fhandle_dbg, { indent(L1), "{" });
      $fdisplay(fhandle_dbg, { indent(L2), "PROVIDE(__debugger_stack_start = .);" });
      $fdisplay(fhandle_dbg, { indent(L2), ". = ", $sformatf("0x%2x;", DEBUG_STACK_OFFSET) });
      $fdisplay(fhandle_dbg, { indent(L1), "} >dbg" });
    end

    $fdisplay(fhandle_dbg, "}");

    $fclose(fhandle_dbg);

    // ############################################################
    // Generate sections extras file
    // ############################################################

    // Include all valid regions in memory layout, set non-executable regions as noload for simplicity
    if (CORE_PARAM_PMA_NUM_REGIONS > 1 || (CORE_PARAM_PMA_NUM_REGIONS == 1 && !disable_default_ram_region)) begin
      $fdisplay(fhandle_pma, "SECTIONS");
      $fdisplay(fhandle_pma, "{");

      foreach (pma_adapted_memory.region[i]) begin

        if (!(pma_adapted_memory.region[i].cfg.main)) begin
          section_location = "(NOLOAD)";
        end else begin
          section_location = $sformatf("(ORIGIN(region_%0d))", i);
        end

        // Write to section_extra.ld, special case for aliased region, will cause overlap if explicitly created
        if (disable_section_write == 0) begin
          $fdisplay(fhandle_pma, { indent(L1), ".region_", $sformatf("%0d %0s", i, section_location), ":" });
          $fdisplay(fhandle_pma, { indent(L1), "{" });
          $fdisplay(fhandle_pma, { indent(L2), "KEEP(*(.region_", $sformatf("%0d", i), "));" });
          $fdisplay(fhandle_pma, { indent(L1), "} > region_", $sformatf("%0d", i) });
        end else begin
          disable_section_write = 0;
        end
      end
      $fdisplay(fhandle_pma, "}");
    end

    $fclose(fhandle_pma);

    // ############################################################
    // Generate fixed address sections
    // ############################################################

    foreach (pma_adapted_memory.region[i]) begin
      if (BOOT_ADDR inside { [pma_adapted_memory.region[i].cfg.word_addr_low : pma_adapted_memory.region[i].cfg.word_addr_high] }) begin
        boot_region = i;
      end
      if (NMI_ADDR inside  { [pma_adapted_memory.region[i].cfg.word_addr_low : pma_adapted_memory.region[i].cfg.word_addr_high] }) begin
        nmi_region = i;
      end
    end //foreach

    if (nmi_region != -1) begin
      nmi_memory_area = $sformatf("region_%0d", nmi_region);
    end else begin
      nmi_memory_area = "";
    end

    $fdisplay(fhandle_fix, "SECTIONS");
    $fdisplay(fhandle_fix, "{");
    $fdisplay(fhandle_fix, { indent(L1), "/* CORE-V: we want a fixed entry point */" });
    $fdisplay(fhandle_fix, { indent(L1), "PROVIDE(__boot_address = ", $sformatf("0x%08x", BOOT_ADDR), ");" });
    $fdisplay(fhandle_fix, { indent(L1), "/* NMI interrupt handler fixed entry point */" });
    $fdisplay(fhandle_fix, { indent(L1), "PROVIDE(nmi_handler = ", $sformatf("0x%8x", NMI_ADDR), ");" });
    $fdisplay(fhandle_fix, { indent(L1), ".nmi :" });
    $fdisplay(fhandle_fix, { indent(L1), "{" });
    $fdisplay(fhandle_fix, { indent(L2), "KEEP(*(.nmi));" });
    $fdisplay(fhandle_fix, { indent(L1), "} > ", nmi_memory_area });
    $fdisplay(fhandle_fix, "}");

    $fclose(fhandle_fix);

    // ############################################################
    // Generate yaml configurations
    // ############################################################

    // The overrides specified here is not necessary in the current implementation of the ISS, leaving this here, albeit disabled
    // if examples of this functionality is needed in the future.
    if (CREATE_YAML_CFG == 1) begin
      $display(pma_cfg_name);
      fhandle_yaml = $fopen({pma_cfg_name, ".yaml"},  "w");
      if (!fhandle_yaml) begin
        `uvm_fatal("DEBUG", $sformatf("Unable to open %s.yaml", pma_cfg_name));
      end
      $fdisplay(fhandle_yaml, {"name: ", pma_cfg_name});
      $fdisplay(fhandle_yaml, {"description: PMA configuration for the ", pma_cfg_name.toupper, " test case"});
      $fdisplay(fhandle_yaml,  "compile_flags: ");
      $fdisplay(fhandle_yaml, {indent(L1), "+define+", pma_cfg_name.toupper});
      if (CREATE_YAML_OVP_OVERRIDES == 1) begin
        $fdisplay(fhandle_yaml,  "ovpsim: >");
        $fdisplay(fhandle_yaml, {indent(L1), "--override root/cpu/extension/PMA_NUM_REGIONS=", $sformatf("%0d", CORE_PARAM_PMA_NUM_REGIONS)});
        foreach (CORE_PARAM_PMA_CFG[i]) begin
          $fdisplay(fhandle_yaml, {indent(L1), "--override root/cpu/extension/word_addr_low",  $sformatf("%0d=0x%08x", i, CORE_PARAM_PMA_CFG[i].word_addr_low)});
          $fdisplay(fhandle_yaml, {indent(L1), "--override root/cpu/extension/word_addr_high", $sformatf("%0d=0x%08x", i, CORE_PARAM_PMA_CFG[i].word_addr_high)});
          $fdisplay(fhandle_yaml, {indent(L1), "--override root/cpu/extension/main",           $sformatf("%0d=%0d",    i, CORE_PARAM_PMA_CFG[i].main)});
          $fdisplay(fhandle_yaml, {indent(L1), "--override root/cpu/extension/bufferable",     $sformatf("%0d=%0d",    i, CORE_PARAM_PMA_CFG[i].bufferable)});
          $fdisplay(fhandle_yaml, {indent(L1), "--override root/cpu/extension/cacheable",      $sformatf("%0d=%0d",    i, CORE_PARAM_PMA_CFG[i].cacheable)});
          $fdisplay(fhandle_yaml, {indent(L1), "--override root/cpu/extension/atomic",         $sformatf("%0d=%0d",    i, CORE_PARAM_PMA_CFG[i].atomic)});
        end
      end
      $fclose(fhandle_yaml);
    end
    uvm_config_db#(bit)::set(.cntxt(null), .inst_name("*"), .field_name("tp"), .value(1'b1));
    uvm_config_db#(bit)::set(.cntxt(null), .inst_name("*"), .field_name("evalid"), .value(1'b1));
    uvm_config_db#(bit[31:0])::set(.cntxt(null), .inst_name("*"), .field_name("evalue"), .value(1'b0));
    uvm_config_db#(bit)::set(null, "", "sim_finished", 1);
  end


  /*
  *  END LDGEN
  */

   /**
    * End-of-test summary printout.
    */
   final begin: end_of_test
      string             summary_string;
      uvm_report_server  rs;
      int                err_count;
      int                warning_count;
      int                fatal_count;
      static bit         sim_finished = 0;

      static string  red   = "\033[31m\033[1m";
      static string  green = "\033[32m\033[1m";
      static string  reset = "\033[0m";

      rs            = uvm_top.get_report_server();
      err_count     = rs.get_severity_count(UVM_ERROR);
      warning_count = rs.get_severity_count(UVM_WARNING);
      fatal_count   = rs.get_severity_count(UVM_FATAL);

      void'(uvm_config_db#(bit)::get(null, "", "sim_finished", sim_finished));

      $display("\n%m: *** Test Summary ***\n");

      if (sim_finished && (err_count == 0) && (fatal_count == 0)) begin
         $display("    PPPPPPP    AAAAAA    SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
         $display("    PP    PP  AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
         $display("    PP    PP  AA    AA  SS        SS        EE        DD    DD    ");
         $display("    PPPPPPP   AAAAAAAA   SSSSSS    SSSSSS   EEEEE     DD    DD    ");
         $display("    PP        AA    AA        SS        SS  EE        DD    DD    ");
         $display("    PP        AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
         $display("    PP        AA    AA   SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
         $display("    ----------------------------------------------------------");
         if (warning_count == 0) begin
           $display("                        SIMULATION PASSED                     ");
         end
         else begin
           $display("                 SIMULATION PASSED with WARNINGS              ");
         end
         $display("    ----------------------------------------------------------");
      end
      else begin
         $display("    FFFFFFFF   AAAAAA   IIIIII  LL        EEEEEEEE  DDDDDDD       ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FFFFF     AAAAAAAA    II    LL        EEEEE     DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA  IIIIII  LLLLLLLL  EEEEEEEE  DDDDDDD       ");

         if (sim_finished == 0) begin
            $display("    --------------------------------------------------------");
            $display("                   SIMULATION FAILED - ABORTED              ");
            $display("    --------------------------------------------------------");
         end
         else begin
            $display("    --------------------------------------------------------");
            $display("                       SIMULATION FAILED                    ");
            $display("    --------------------------------------------------------");
         end
      end
   end

endmodule : uvmt_cv32e40x_ldgen_tb
`default_nettype wire

`endif // __UVMT_CV32E40X_LDGEN_TB_SV__


