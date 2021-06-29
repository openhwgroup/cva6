/**
 * Quasi-static core control signals.
 */
interface uvme_cv32e40x_core_cntrl_if 
    import uvm_pkg::*;
    import cv32e40x_pkg::*;
    ();

    logic        clk;
    logic        fetch_en;
                                        
    logic        scan_cg_en;
    logic [31:0] boot_addr;
    logic [31:0] mtvec_addr;
    logic [31:0] dm_halt_addr;
    logic [31:0] dm_exception_addr;
    logic [31:0] nmi_addr;
    logic [31:0] hart_id;

    logic [31:0] num_mhpmcounters;    

    // Testcase asserts this to load memory (not really a core control signal)
    logic        load_instr_mem;
    pma_region_t pma_cfg[];

  covergroup core_cntrl_cg;

    boot_address: coverpoint boot_addr {
      bins low  = {[32'h0000_0000 : 32'h0000_FFFF]};
      bins med  = {[32'h0001_0000 : 32'hEFFF_FFFF]};
      bins high = {[32'hF000_0000 : 32'hFFFF_FFFF]};
    }
    mtvec_address: coverpoint mtvec_addr {
      bins low  = {[32'h0000_0000 : 32'h0000_FFFF]};
      bins med  = {[32'h0001_0000 : 32'hEFFF_FFFF]};
      bins high = {[32'hF000_0000 : 32'hFFFF_FFFF]};
    }
    debug_module_halt_address: coverpoint dm_halt_addr {
      bins low  = {[32'h0000_0000 : 32'h0000_FFFF]};
      bins med  = {[32'h0001_0000 : 32'hEFFF_FFFF]};
      bins high = {[32'hF000_0000 : 32'hFFFF_FFFF]};
    }
    debug_module_exception_address: coverpoint dm_exception_addr {
      bins low  = {[32'h0000_0000 : 32'h0000_FFFF]};
      bins med  = {[32'h0001_0000 : 32'hEFFF_FFFF]};
      bins high = {[32'hF000_0000 : 32'hFFFF_FFFF]};
    }
    hart_id: coverpoint hart_id {
      bins low  = {[32'h0000_0000 : 32'h0000_FFFF]};
      bins med  = {[32'h0001_0000 : 32'hEFFF_FFFF]};
      bins high = {[32'hF000_0000 : 32'hFFFF_FFFF]};
    }

  endgroup: core_cntrl_cg

  core_cntrl_cg core_cntrl_cg_inst = new();

  clocking drv_cb @(posedge clk);
    output fetch_en;
  endclocking : drv_cb

endinterface : uvme_cv32e40x_core_cntrl_if
