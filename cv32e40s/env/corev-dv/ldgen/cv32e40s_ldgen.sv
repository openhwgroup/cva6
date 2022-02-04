/*
 * Copyright 2021 Silicon Labs, Inc.
 *
 * This file, and derivatives thereof are licensed under the
 * Solderpad License, Version 2.0 (the "License");
 * Use of this file means you agree to the terms and conditions
 * of the license and are in full compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://solderpad.org/licenses/SHL-2.0/
 *
 * Unless required by applicable law or agreed to in writing, software
 * and hardware implementations thereof
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * provide UVM environment entry and exit points.
 */
import cv32e40s_pkg::pma_region_t;

  class cv32e40s_ldgen_c;

    // Output file names
    parameter string MEMORY_LAYOUT_FILE   = "linkcmds.memory";
    parameter string SECTIONS_PMA_FILE    = "linkcmds.pmasec";
    parameter string SECTIONS_DEBUG_FILE  = "linkcmds.dbgsec";
    parameter string FIXED_ADDR_FILE      = "linkcmds.fixadd";

    // Num regions = 0 |-> pma disabled |-> default corev-dv behavior of 2 PMA regions
    parameter PMA_NUM_REGIONS = CORE_PARAM_PMA_NUM_REGIONS ? CORE_PARAM_PMA_NUM_REGIONS : 2;

    // indentation level widths
    parameter L1                   = 3;
    parameter L2                   = 6;

    // Memory support - when enabled, the linker script gets code regions set to their
    // full extent specified by the PMA configuration - alternatively this can be disabled
    // to restrict memory regions to a certain size (4096*64 bytes per region default)
    parameter LARGE_MEMORY_SUPPORT = 0;
    parameter SMALL_MEM_LIMIT      = 'h12_0000;

    // Default addresses
    parameter RAM_ORIGIN           = 32'h0000_0000;
    parameter RAM_LENGTH           = 32'h40_0000;
    parameter BOOT_ADDR            = 32'h80;
    parameter NMI_ADDR             = 32'h0010_0000;
    parameter MTVEC_ADDR           = 32'h0000_0000;
    parameter DEBUG_ORIGIN         = 32'h1A11_0800;
    parameter DEBUG_EXCEPTION_ADDR = 32'h1A11_1000;
    parameter DEBUG_STACK_OFFSET   = 32'h80;

    // Disable default regions - disabled ram is the default, as we alias another executable
    // region to take its place.
    parameter DISABLE_DEFAULT_RAM_REGION = 1;
    parameter DISABLE_DEFAULT_DBG_REGION = 0;

    static string info_tag = "ldgen";
    static string default_attributes = "(rwxai)";

    // Path handles
    string ldfiles_path;

    bit disable_default_ram_region;
    bit disable_default_dbg_region;
    bit enable_large_mem_support;
    bit nmi_separate_region;

    int disable_section_write_boot = 0;
    int disable_section_write_nmi  = 0;
    int region_length;
    string nmi_memory_area;
    string mtvec_memory_area;
    string region_attributes;
    string section_location;

    // Fixed addresses
    int unsigned boot_addr;
    int unsigned nmi_addr;
    int unsigned mtvec_addr;
    int unsigned dbg_origin_addr;
    int unsigned dbg_exception_addr;
    int unsigned dbg_stack_offset;

    // Test parameters (for multi-generation passes)
    bit start_idx_valid;
    int start_idx;
    int num_of_tests;

    // File handles
    int fhandle_mem;
    int fhandle_pma;
    int fhandle_dbg;
    int fhandle_fix;

    pma_region_t regions[PMA_NUM_REGIONS][$];
    pma_region_t temp_region;
    int temp_region_ctr;
    pma_adapted_memory_regions_c pma_adapted_memory;

    extern function string indent(int num_indent);
    extern function void create_memory_layout_file(string filepath);
    extern function void create_pma_section_file(string filepath);
    extern function void create_dbg_section_file(string filepath);
    extern function void create_fixed_addr_section_file(string filepath);
    extern function void gen_pma_linker_scripts();
    extern function void display_fatal(string text);
    extern function void display_message(string text);

    function new();
      pma_adapted_memory = new(CORE_PARAM_PMA_CFG);
      pma_adapted_memory.check_regions;

      // Use defaults if not overridden by plusargs
      if (!($value$plusargs("boot_addr=0x%x", boot_addr))) begin
        boot_addr = BOOT_ADDR;
      end
      if (!($value$plusargs("nmi_addr=0x%x", nmi_addr))) begin
        nmi_addr = NMI_ADDR;
      end
      if (!($value$plusargs("mtvec_addr=0x%x", mtvec_addr))) begin
        mtvec_addr = MTVEC_ADDR;
      end
      if (!($value$plusargs("dm_halt_addr=0x%x", dbg_origin_addr))) begin
        dbg_origin_addr = DEBUG_ORIGIN;
      end
      if (!($value$plusargs("dm_exception_addr=0x%x", dbg_exception_addr))) begin
        dbg_exception_addr = DEBUG_EXCEPTION_ADDR;
      end
      if (!($value$plusargs("debug_stack_offset=0x%x", dbg_stack_offset))) begin
        dbg_stack_offset = DEBUG_STACK_OFFSET;
      end
      if (!($value$plusargs("disable_default_ram_region=%d", disable_default_ram_region))) begin
        disable_default_ram_region = CORE_PARAM_PMA_NUM_REGIONS ? DISABLE_DEFAULT_RAM_REGION : 0;
      end
      if (!($value$plusargs("disable_default_dbg_region=%d", disable_default_dbg_region))) begin
        disable_default_dbg_region = DISABLE_DEFAULT_DBG_REGION;
      end
      if (!($value$plusargs("enable_large_mem_support=%d", enable_large_mem_support))) begin
        enable_large_mem_support = LARGE_MEMORY_SUPPORT;
      end

      if ($value$plusargs("ldgen_cp_test_path=%s", ldfiles_path)) begin
        if ($value$plusargs("start_idx=%d", start_idx)) begin
          start_idx_valid = 1;
          if (!$value$plusargs("num_of_tests=%d", num_of_tests)) begin
            display_fatal("Must specify +num_of_tests with +start_idx and +ldgen_cp_test_path");
          end
        end
      end

    endfunction : new

endclass : cv32e40s_ldgen_c

//--------------------------------------------------------------------------------

function void cv32e40s_ldgen_c::display_fatal(string text);
  `ifdef uvm_fatal
    `uvm_fatal(info_tag, text)
  `else
    $fatal(1, { "[", info_tag, "] ", text });
  `endif
endfunction : display_fatal

//--------------------------------------------------------------------------------

function void cv32e40s_ldgen_c::display_message(string text);
  `ifdef uvm_info
    `uvm_info(info_tag, text, UVM_LOW)
  `else
    $display({ "[", info_tag, "] ", text });
  `endif
endfunction : display_message

//--------------------------------------------------------------------------------

function void cv32e40s_ldgen_c::gen_pma_linker_scripts();

  // If no ldfiles path was configured then emit files to simulation run directory
  if (ldfiles_path == "") begin
    create_fixed_addr_section_file(FIXED_ADDR_FILE);
    create_memory_layout_file(MEMORY_LAYOUT_FILE);
    create_pma_section_file(SECTIONS_PMA_FILE);
    create_dbg_section_file(SECTIONS_DEBUG_FILE);
  end
  else if (start_idx_valid) begin
    // Iteratively generate the files to indexed directories
    // Yes, this is wasteful but overall ldgen is fast so we can live with this
    for (int idx = start_idx; idx < start_idx + num_of_tests; idx++) begin
      string fixed_addr_file     = $sformatf("%s/%0d/test_program/%s", ldfiles_path, idx, FIXED_ADDR_FILE);
      string memory_layout_file  = $sformatf("%s/%0d/test_program/%s", ldfiles_path, idx, MEMORY_LAYOUT_FILE);
      string sections_pma_file   = $sformatf("%s/%0d/test_program/%s", ldfiles_path, idx, SECTIONS_PMA_FILE);
      string sections_debug_file = $sformatf("%s/%0d/test_program/%s", ldfiles_path, idx, SECTIONS_DEBUG_FILE);

      create_fixed_addr_section_file(fixed_addr_file);
      create_memory_layout_file(memory_layout_file);
      create_pma_section_file(sections_pma_file);
      create_dbg_section_file(sections_debug_file);
    end
  end
  else begin
    // Emit files to fixed path
    string fixed_addr_file     = $sformatf("%s/%s", ldfiles_path, FIXED_ADDR_FILE);
    string memory_layout_file  = $sformatf("%s/%s", ldfiles_path, MEMORY_LAYOUT_FILE);
    string sections_pma_file   = $sformatf("%s/%s", ldfiles_path, SECTIONS_PMA_FILE);
    string sections_debug_file = $sformatf("%s/%s", ldfiles_path, SECTIONS_DEBUG_FILE);

    create_fixed_addr_section_file(fixed_addr_file);
    create_memory_layout_file(memory_layout_file);
    create_pma_section_file(sections_pma_file);
    create_dbg_section_file(sections_debug_file);
  end
  display_message("Linker scripts gen complete");
endfunction : gen_pma_linker_scripts

//--------------------------------------------------------------------------------

function string cv32e40s_ldgen_c::indent(int num_indent);
  string indent_val;
  indent_val.itoa(num_indent);
  return $sformatf( { "%-", indent_val , "s" } , " " );
endfunction : indent

//--------------------------------------------------------------------------------

function void cv32e40s_ldgen_c::create_memory_layout_file(string filepath);
  automatic int nmi_region = -1;
  automatic int boot_region = -1;

  fhandle_mem = $fopen(filepath,  "w");
  if (!fhandle_mem) begin
    display_fatal($sformatf("Unable to open %s", filepath));
  end

  $fdisplay(fhandle_mem, "MEMORY");
  $fdisplay(fhandle_mem, "{");

  // Optionally disable default ram region definition
  if (!disable_default_ram_region) begin
    $fdisplay(fhandle_mem, { indent(L1), $sformatf("ram (rwxai) : ORIGIN = 0x%08x, LENGTH = 0x%6x", RAM_ORIGIN, RAM_LENGTH) });
  end

  if (!disable_default_dbg_region) begin
    // Debug is not aliased to some other region, so we need to make sure this code is only in place if debug is enabled
    $fdisplay(fhandle_mem, { indent(L1), $sformatf("dbg (rwxai) : ORIGIN = 0x%08x, LENGTH = 0x1000", dbg_origin_addr) });
  end

  if (nmi_separate_region) begin
    // Separate nmi region if not enclosed by any other region
    $fdisplay(fhandle_mem, { indent(L1), $sformatf("nmi (rwxai) : ORIGIN = 0x%08x, LENGTH = 0x1000", nmi_addr) });
  end

  //if (CORE_PARAM_PMA_NUM_REGIONS > 0) begin
  if (pma_adapted_memory.region.size > 0) begin
    foreach (pma_adapted_memory.region[i]) begin

      if (boot_addr inside { [pma_adapted_memory.region[i].cfg.word_addr_low << 2 : pma_adapted_memory.region[i].cfg.word_addr_high << 2] }) begin
        if (pma_adapted_memory.region[i].cfg.main != 1) begin
          display_fatal($sformatf("Boot address is not in executable region!"));
        end
        boot_region = i;
        disable_section_write_boot = i;
      end
      if (LARGE_MEMORY_SUPPORT) begin
        if (nmi_addr inside  { [pma_adapted_memory.region[i].cfg.word_addr_low << 2: pma_adapted_memory.region[i].cfg.word_addr_high << 2] }) begin
          nmi_region = i;
          disable_section_write_nmi = i;
        end
      end else begin
        if (nmi_addr inside  { [pma_adapted_memory.region[i].cfg.word_addr_low << 2: pma_adapted_memory.region[i].cfg.word_addr_high << 2] }) begin
          disable_section_write_nmi = i;
          nmi_region = i;
        end
      end

      if (!(pma_adapted_memory.region[i].cfg.main)) begin
        region_attributes = "(!i)";
      end else begin
        region_attributes = default_attributes;
      end

      // Allow large memory regions if enabled, otherwise restrict to max SMALL_MEM_LIMIT
      if (enable_large_mem_support) begin
        region_length = (pma_adapted_memory.region[i].cfg.word_addr_high << 2) - (pma_adapted_memory.region[i].cfg.word_addr_low << 2);
      end else begin
        if ((pma_adapted_memory.region[i].cfg.word_addr_high << 2) - (pma_adapted_memory.region[i].cfg.word_addr_low << 2) <= SMALL_MEM_LIMIT) begin
          region_length = (pma_adapted_memory.region[i].cfg.word_addr_high << 2) - (pma_adapted_memory.region[i].cfg.word_addr_low << 2);
        end else begin
          region_length = SMALL_MEM_LIMIT;
        end
      end

      // Write to memory.ld
      $fdisplay(fhandle_mem, { indent(L1), $sformatf("region_%0d %-7s : ORIGIN = 0x%08x, LENGTH = 0x%08x",
                                                    i, region_attributes, pma_adapted_memory.region[i].cfg.word_addr_low<<2, region_length) });
    end // foreach

    // Check for invalid configurations, e.g. boot address not executable or nmi-address not in any memory region (code will not be linkable)
    if (boot_region == -1) begin
      display_fatal($sformatf("Boot address (0x%08x) is not in any region, regions not covered by PMA are not executable!", boot_addr));
    end
    if (nmi_region == -1) begin
      display_fatal($sformatf("NMI address (0x%08x) is not in any region, this will cause linker failure!", nmi_addr));
    end
  end

  $fdisplay(fhandle_mem, "}");

  // if the default ram region is enabled, we alias the lowest numbered executable pma region to ram (boot address needs to be set accordingly)
  if (disable_default_ram_region) begin
    $fdisplay(fhandle_mem, { "REGION_ALIAS(\"ram\", region_", $sformatf("%0d", boot_region), ");" });
  end

  $fclose(fhandle_mem);
  display_message({ filepath, " generated" });

endfunction : create_memory_layout_file

//--------------------------------------------------------------------------------

function void cv32e40s_ldgen_c::create_pma_section_file(string filepath);

  fhandle_pma = $fopen(filepath, "w");
  if (!fhandle_pma) begin
    display_fatal($sformatf("Unable to open %s", filepath));
  end

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
      if (!((disable_section_write_boot == i) ||
            (disable_section_write_nmi  == i))) begin
        $fdisplay(fhandle_pma, { indent(L1), ".region_", $sformatf("%0d %0s", i, section_location), ":" });
        $fdisplay(fhandle_pma, { indent(L1), "{" });
        $fdisplay(fhandle_pma, { indent(L2), "KEEP(*(.region_", $sformatf("%0d", i), "));" });
        $fdisplay(fhandle_pma, { indent(L1), "}"});
      end
    end
    $fdisplay(fhandle_pma, "}");
  end

  $fclose(fhandle_pma);
  display_message({ filepath, " generated" });

endfunction : create_pma_section_file

//--------------------------------------------------------------------------------

function void cv32e40s_ldgen_c::create_dbg_section_file(string filepath);
  int dbg_exception_addr_region = -1;
  int dbg_origin_addr_region = -1;

  fhandle_dbg = $fopen(filepath, "w");
  if (!fhandle_dbg) begin
    display_fatal($sformatf("Unable to open %s", filepath));
  end

  // Conditionally create the contents of the debug.ld file, otherwise it will be overwritten with an empty file
  if (!disable_default_dbg_region) begin

    foreach (pma_adapted_memory.region[i]) begin
      if (dbg_exception_addr inside {[pma_adapted_memory.region[i].cfg.word_addr_low<<2:pma_adapted_memory.region[i].cfg.word_addr_high<<2]}) begin
        if (pma_adapted_memory.region[i].cfg.main == 1) begin
          dbg_exception_addr_region = i;
        end
      end
      if (dbg_origin_addr inside {[pma_adapted_memory.region[i].cfg.word_addr_low<<2:pma_adapted_memory.region[i].cfg.word_addr_high<<2]}) begin
        if (pma_adapted_memory.region[i].cfg.main == 1) begin
          dbg_origin_addr_region = i;
        end
      end
    end

    if (dbg_exception_addr_region == -1 && CORE_PARAM_PMA_NUM_REGIONS > 0) begin
      display_fatal($sformatf("dm_exception_addr (0x%08x) is not within an executable region!", dbg_exception_addr));
    end
    if (dbg_origin_addr_region == -1 && CORE_PARAM_PMA_NUM_REGIONS > 0) begin
      display_fatal($sformatf("dm_halt_addr (0x%08x) is not within an executable region!", dbg_origin_addr));
    end

    $fdisplay(fhandle_dbg, "SECTIONS");
    $fdisplay(fhandle_dbg, "{");
    //$fdisplay(fhandle_fix, { indent(L1), "debug_rom = ABSOLUTE(", $sformatf("0x%08x",  nmi_addr), ");" });
    $fdisplay(fhandle_dbg, { indent(L1), "debug_rom = ABSOLUTE(", $sformatf("0x%08x",  dbg_origin_addr), ");" });
    $fdisplay(fhandle_dbg, { indent(L1), "debug_exception = ABSOLUTE(", $sformatf("0x%08x",  dbg_exception_addr), ");" });

    $fdisplay(fhandle_dbg, { indent(L1), ".debugger (ORIGIN(dbg)):" });
    $fdisplay(fhandle_dbg, { indent(L1), "{" });
    $fdisplay(fhandle_dbg, { indent(L2), "KEEP(*(.debugger));" });
    $fdisplay(fhandle_dbg, { indent(L1), "} > dbg" });

    $fdisplay(fhandle_dbg, { indent(L1), ".debugger_exception ", $sformatf("(0x%08x):", dbg_exception_addr) });
    $fdisplay(fhandle_dbg, { indent(L1), "{" });
    $fdisplay(fhandle_dbg, { indent(L2), "KEEP(*(.debugger_exception));" });
    $fdisplay(fhandle_dbg, { indent(L1), "} > dbg" });

    $fdisplay(fhandle_dbg, { indent(L1), ".debugger_stack : ALIGN(16)" });
    $fdisplay(fhandle_dbg, { indent(L1), "{" });
    $fdisplay(fhandle_dbg, { indent(L2), "PROVIDE(__debugger_stack_start = .);" });
    $fdisplay(fhandle_dbg, { indent(L2), ". = ", $sformatf("0x%2x;", dbg_stack_offset) });
    $fdisplay(fhandle_dbg, { indent(L1), "} > dbg" });
    $fdisplay(fhandle_dbg, "}");
  end

  $fclose(fhandle_dbg);
  display_message({ filepath, " generated" });
endfunction

//--------------------------------------------------------------------------------

function void cv32e40s_ldgen_c::create_fixed_addr_section_file(string filepath);
  automatic int nmi_region   = -1;
  automatic int boot_region  = -1;
  automatic int mtvec_region = -1;
  automatic int nmi_region_half_length;

  fhandle_fix = $fopen(filepath, "w");
  if (!fhandle_fix) begin
    display_fatal($sformatf("Unable to open %s", filepath));
  end
  if (pma_adapted_memory.region.size == 0) begin
    nmi_separate_region = 1;
  end

  foreach (pma_adapted_memory.region[i]) begin
    if (mtvec_addr inside { [pma_adapted_memory.region[i].cfg.word_addr_low << 2 : pma_adapted_memory.region[i].cfg.word_addr_high << 2] }) begin
      if ((!enable_large_mem_support && ((pma_adapted_memory.region[i].cfg.word_addr_low << 2) + mtvec_addr < SMALL_MEM_LIMIT)) ||
            enable_large_mem_support) begin
        mtvec_region = i;
      end
    end
    if (boot_addr inside { [pma_adapted_memory.region[i].cfg.word_addr_low << 2 : pma_adapted_memory.region[i].cfg.word_addr_high << 2] }) begin
      if ((!enable_large_mem_support && ((pma_adapted_memory.region[i].cfg.word_addr_low << 2) + boot_addr < SMALL_MEM_LIMIT)) ||
            enable_large_mem_support) begin
        boot_region = i;
      end
    end
    if (nmi_addr inside  { [pma_adapted_memory.region[i].cfg.word_addr_low << 2: pma_adapted_memory.region[i].cfg.word_addr_high << 2] }) begin
      if ((!enable_large_mem_support && (nmi_addr - (pma_adapted_memory.region[i].cfg.word_addr_low << 2) < SMALL_MEM_LIMIT)) ||
            enable_large_mem_support) begin
        nmi_region = i;
      end else begin
        nmi_separate_region = 1;
      end
    end
  end //foreach

  if (mtvec_region != -1) begin
    mtvec_memory_area = $sformatf(" > region_%0d", mtvec_region);
  end else begin
    mtvec_memory_area = "";
  end

  if (nmi_region != -1) begin
    nmi_memory_area = $sformatf(" > region_%0d", nmi_region);
    // Find which part of region the fixed handlers reside, this is to ensure that we have space to place the remaining section code
    nmi_region_half_length = ((pma_adapted_memory.region[nmi_region].cfg.word_addr_high << 2) - (pma_adapted_memory.region[nmi_region].cfg.word_addr_low << 2)) / 2;
  end else if (nmi_separate_region) begin
    nmi_memory_area = " > nmi";
  end else begin
    nmi_memory_area = "";
  end

  $fdisplay(fhandle_fix, "SECTIONS");
  $fdisplay(fhandle_fix, "{");
  $fdisplay(fhandle_fix, { indent(L1), "/* CORE-V: interrupt vectors */" });
  $fdisplay(fhandle_fix, { indent(L1), "PROVIDE(__vector_start = ", $sformatf("0x%08x", mtvec_addr), ");" });
  $fdisplay(fhandle_fix, { indent(L1), ".mtvec_bootstrap (__vector_start) :" });
  $fdisplay(fhandle_fix, { indent(L1), "{" });
  $fdisplay(fhandle_fix, { indent(L2), "KEEP(*(.mtvec_bootstrap));" });
  $fdisplay(fhandle_fix, { indent(L1), "}", mtvec_memory_area, "\n" });
  $fdisplay(fhandle_fix, { indent(L1), "/* CORE-V: we want a fixed entry point */" });
  $fdisplay(fhandle_fix, { indent(L1), "PROVIDE(__boot_address = ", $sformatf("0x%08x", boot_addr), ");\n" });
  $fdisplay(fhandle_fix, { indent(L1), "/* NMI interrupt handler fixed entry point */" });
  $fdisplay(fhandle_fix, { indent(L1), "nmi_handler = ABSOLUTE(", $sformatf("0x%08x",  nmi_addr), ");" });
  $fdisplay(fhandle_fix, { indent(L1), ".nmi (", $sformatf("0x%08x", nmi_addr), ") :" });
  $fdisplay(fhandle_fix, { indent(L1), "{" });
  $fdisplay(fhandle_fix, { indent(L2), "KEEP(*(.nmi));" });
  $fdisplay(fhandle_fix, { indent(L1), "}", nmi_memory_area });
  $fdisplay(fhandle_fix, "}");

  $fclose(fhandle_fix);
  display_message({ filepath, " generated" });

endfunction : create_fixed_addr_section_file
