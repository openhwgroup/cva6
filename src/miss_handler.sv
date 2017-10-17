// --------------
// MISS Handler
// --------------
//
// Description: Handles cache misses.
//
import nbdcache_pkg::*;

module miss_handler #(
    parameter int unsigned NR_PORTS = 3
)(
    input  logic                                        clk_i,
    input  logic                                        rst_ni,
    input  logic [NR_PORTS-1:0][$bits(miss_req_t)-1:0]  miss_req_i,
    output logic      [NR_PORTS-1:0]                    miss_gnt_o,
    output logic      [NR_PORTS-1:0]                    miss_valid_o,
    output logic [NR_PORTS-1:0][63:0]                   miss_data_o,
    AXI_BUS.Master                                      bypass_if
    // update cache
);

    // ------------------
    // Cacheline Refills
    // ------------------

    // ------------------
    // Bypass
    // ------------------
    // AXI Adapter
    // request from FSM

    // Hack as system verilog support in modelsim seems to be buggy here
    miss_req_t                   miss_req;
    assign miss_req = miss_req_t'(miss_req_i);

    miss_req_t                   req_fsm_bypass;
    logic                        gnt_bypass_fsm;
    logic                        valid_bypass_fsm;
    logic [63:0]                 data_bypass_fsm;
    logic [$clog2(NR_PORTS)-1:0] id_bypass_fsm, id_fsm_bypass;

    miss_arbiter i_bypass_arbiter (
        // Master Side
        .data_req_i    ( miss_req.valid & miss_req.bypass ),
        .address_i     ( miss_req.addr                      ),
        .data_wdata_i  ( miss_req.wdata                     ),
        .data_we_i     ( miss_req.we                        ),
        .data_be_i     ( miss_req.be                        ),
        .data_gnt_o    ( miss_gnt_o                           ),
        .data_rvalid_o ( miss_valid_o                         ),
        .data_rdata_o  ( miss_data_o                          ),
        // Slave Side
        .id_i          ( id_bypass_fsm                        ),
        .id_o          ( id_fsm_bypass                        ),
        .address_o     ( req_fsm_bypass.addr                  ),
        .data_wdata_o  ( req_fsm_bypass.wdata                 ),
        .data_req_o    ( req_fsm_bypass.valid                 ),
        .data_we_o     ( req_fsm_bypass.we                    ),
        .data_be_o     ( req_fsm_bypass.be                    ),
        .data_gnt_i    ( gnt_bypass_fsm                       ),
        .data_rvalid_i ( valid_bypass_fsm                     ),
        .data_rdata_i  ( data_bypass_fsm                      ),
        .*
    );

    axi_adapter i_bypass_axi_adapter (
        .req_i               ( miss_req.valid     ),
        .type_i              ( SINGLE_REQ           ),
        .gnt_o               ( gnt_bypass_fsm       ),
        .addr_i              ( req_fsm_bypass.addr  ),
        .we_i                ( req_fsm_bypass.we    ),
        .wdata_i             ( req_fsm_bypass.wdata ),
        .be_i                ( req_fsm_bypass.be    ),
        .id_i                ( id_fsm_bypass        ),
        .valid_o             ( miss_valid_o         ),
        .rdata_o             ( miss_data_o          ),
        .id_o                ( id_bypass_fsm        ),
        .critical_word_o     (                      ), // not used for single requests
        .critical_word_valid (                      ), // not used for single requests
        .axi                 ( bypass_if            ),
        .*
    );

endmodule
