// --------------
// MISS Handler
// --------------
//
// Description: Handles cache misses.
//
import nbdcache_pkg::*;

module miss_handler #(
    parameter int unsigned NR_PORTS          = 3,
    parameter int unsigned CACHE_LINE_WIDTH  = 256,
    parameter int unsigned AXI_ID_WIDTH      = 10,
    parameter int unsigned AXI_USER_WIDTH    = 10
)(
    input  logic                                        clk_i,
    input  logic                                        rst_ni,
    input  logic [NR_PORTS-1:0][$bits(miss_req_t)-1:0]  miss_req_i,
    output logic [NR_PORTS-1:0]                         miss_gnt_o,
    output logic [NR_PORTS-1:0]                         miss_valid_o,
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


    logic [NR_PORTS-1:0]        miss_req_valid;
    logic [NR_PORTS-1:0]        miss_req_bypass;
    logic [NR_PORTS-1:0][63:0]  miss_req_addr;
    logic [NR_PORTS-1:0][63:0]  miss_req_wdata;
    logic [NR_PORTS-1:0]        miss_req_we;
    logic [NR_PORTS-1:0][7:0]   miss_req_be;

    logic         req_fsm_bypass_valid;
    logic         req_fsm_bypass_bypass;
    logic [63:0]  req_fsm_bypass_addr;
    logic [63:0]  req_fsm_bypass_wdata;
    logic         req_fsm_bypass_we;
    logic [7:0]   req_fsm_bypass_be;

    // Hack as system verilog support in modelsim seems to be buggy here
    always_comb begin
        automatic miss_req_t miss_req;

        for (int unsigned i = 0; i < NR_PORTS; i++) begin
            miss_req =  miss_req_t'(miss_req_i[i]);
            miss_req_valid  [i]  = miss_req.valid;
            miss_req_bypass [i]  = miss_req.bypass;
            miss_req_addr   [i]  = miss_req.addr;
            miss_req_wdata  [i]  = miss_req.wdata;
            miss_req_we     [i]  = miss_req.we;
            miss_req_be     [i]  = miss_req.be;
        end
    end


    logic                                     gnt_bypass_fsm;
    logic                                     valid_bypass_fsm;
    logic [(CACHE_LINE_WIDTH/64)-1:0][63:0]   data_bypass_fsm;
    logic [$clog2(NR_PORTS)-1:0]              id_fsm_bypass;
    logic [AXI_ID_WIDTH-1:0]                  id_bypass_fsm;

    miss_arbiter #(
            .NR_PORTS  ( NR_PORTS                             )
        ) i_bypass_arbiter (
        // Master Side
        .data_req_i    ( miss_req_valid & miss_req_bypass     ),
        .address_i     ( miss_req_addr                        ),
        .data_wdata_i  ( miss_req_wdata                       ),
        .data_we_i     ( miss_req_we                          ),
        .data_be_i     ( miss_req_be                          ),
        .data_gnt_o    ( miss_gnt_o                           ),
        .data_rvalid_o ( miss_valid_o                         ),
        .data_rdata_o  ( miss_data_o                          ),
        // Slave Side
        .id_i          ( id_bypass_fsm[$clog2(NR_PORTS)-1:0]  ),
        .id_o          ( id_fsm_bypass                        ),
        .address_o     ( req_fsm_bypass_addr                  ),
        .data_wdata_o  ( req_fsm_bypass_wdata                 ),
        .data_req_o    ( req_fsm_bypass_valid                 ),
        .data_we_o     ( req_fsm_bypass_we                    ),
        .data_be_o     ( req_fsm_bypass_be                    ),
        .data_gnt_i    ( gnt_bypass_fsm                       ),
        .data_rvalid_i ( valid_bypass_fsm                     ),
        .data_rdata_i  ( data_bypass_fsm[0]                   ),
        .*
    );

    axi_adapter #(
        .CACHE_LINE_WIDTH   ( CACHE_LINE_WIDTH ),
        .AXI_ID_WIDTH       ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH     ( AXI_USER_WIDTH   )
    ) i_bypass_axi_adapter (
        .req_i               ( req_fsm_bypass_valid                                     ),
        .type_i              ( SINGLE_REQ                                               ),
        .gnt_o               ( gnt_bypass_fsm                                           ),
        .addr_i              ( req_fsm_bypass_addr                                      ),
        .we_i                ( req_fsm_bypass_we                                        ),
        .wdata_i             ( {{{CACHE_LINE_WIDTH-64}{1'b0}}, req_fsm_bypass_wdata}    ),
        .be_i                ( {{{CACHE_LINE_WIDTH/8-8}{1'b0}}, req_fsm_bypass_be}      ),
        .id_i                ( {{{AXI_ID_WIDTH-$clog2(NR_PORTS)}{1'b0}}, id_fsm_bypass} ),
        .valid_o             ( valid_bypass_fsm                                         ),
        .rdata_o             ( data_bypass_fsm                                          ),
        .id_o                ( id_bypass_fsm                                            ),
        .critical_word_o     (                                                          ), // not used for single requests
        .critical_word_valid (                                                          ), // not used for single requests
        .axi                 ( bypass_if                                                ),
        .*
    );

endmodule
