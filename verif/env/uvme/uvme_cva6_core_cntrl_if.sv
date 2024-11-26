/**
 * Quasi-static core control signals.
 */
interface uvme_cva6_core_cntrl_if
    import uvm_pkg::*;
    import uvme_cva6_pkg::*;
    ();

    logic        clk;

    logic [XLEN-1:0] boot_addr;

endinterface : uvme_cva6_core_cntrl_if
