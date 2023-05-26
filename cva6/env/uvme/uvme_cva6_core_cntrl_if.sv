/**
 * Quasi-static core control signals.
 */
interface uvme_cva6_core_cntrl_if
    import uvm_pkg::*;
    import uvme_cva6_pkg::*;
    ();

    logic        clk;
    logic        fetch_en;

    logic        scan_cg_en;
    logic [XLEN-1:0] boot_addr;
    logic [XLEN-1:0] mtvec_addr;
    logic [XLEN-1:0] dm_halt_addr;
    logic [XLEN-1:0] dm_exception_addr;
    logic [XLEN-1:0] nmi_addr;
    logic [XLEN-1:0] mhartid;
    logic [XLEN-1:0] mimpid;

    logic [XLEN-1:0] num_mhpmcounters;
    //~ pma_region_t pma_cfg[];

    // Testcase asserts this to load memory (not really a core control signal)
    logic        load_instr_mem;

  clocking drv_cb @(posedge clk);
    output fetch_en;
  endclocking : drv_cb

endinterface : uvme_cva6_core_cntrl_if
