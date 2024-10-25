`include "axi/typedef.svh"
`include "axi/assign.svh"

`include "ariane_xlnx_config.svh"
`include "ariane_xlnx_mapper.svh"

import cva6_config_pkg::*;

module debug_module_wrapper#(
    parameter AXI_ID_WIDTH   = 10,
    parameter AXI_ADDR_WIDTH = 64,
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_USER_WIDTH = 1
)
(
    input logic aclk,
    input logic aresetn,

    `AXI_INTERFACE_MODULE_INPUT(s_axi_dmi_jtag),
    `AXI_INTERFACE_MODULE_OUTPUT(m_axi_dmi_jtag),

    // jtag ports
    input  logic        trst_n,
    input  logic        tck,
    input  logic        tms,
    input  logic        tdi,
    output wire         tdo,

    // to CPU/other peripherals
    output logic ndmreset,
    output logic debug_req_irq
);

import ariane_axi::req_t;
import ariane_axi::resp_t;

ariane_axi::req_t    dm_axi_m_req;
ariane_axi::resp_t   dm_axi_m_resp;

logic test_en;
assign test_en = 1'b0;

logic          debug_req_valid;
logic          debug_req_ready;
dm::dmi_req_t  debug_req;
logic          debug_resp_valid;
logic          debug_resp_ready;
dm::dmi_resp_t debug_resp;

logic dmactive;

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH          ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH          ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH            ),
    .AXI_USER_WIDTH ( AXI_DATA_WIDTH          )
) slave_bus (), master_bus();

// ---------------
// Debug Module
// ---------------
dmi_jtag i_dmi_jtag (
    .clk_i                ( aclk                 ),
    .rst_ni               ( aresetn              ),
    .dmi_rst_no           (                      ), // keep open
    .testmode_i           ( test_en              ),
    .dmi_req_valid_o      ( debug_req_valid      ),
    .dmi_req_ready_i      ( debug_req_ready      ),
    .dmi_req_o            ( debug_req            ),
    .dmi_resp_valid_i     ( debug_resp_valid     ),
    .dmi_resp_ready_o     ( debug_resp_ready     ),
    .dmi_resp_i           ( debug_resp           ),
    .tck_i                ( tck    ),
    .tms_i                ( tms    ),
    .trst_ni              ( trst_n ),
    .td_i                 ( tdi    ),
    .td_o                 ( tdo    ),
    .tdo_oe_o             (        )
);

logic                       dm_slave_req;
logic                       dm_slave_we;
logic [CVA6Cfg.XLEN-1:0]    dm_slave_addr;
logic [CVA6Cfg.XLEN/8-1:0]  dm_slave_be;
logic [CVA6Cfg.XLEN-1:0]    dm_slave_wdata;
logic [CVA6Cfg.XLEN-1:0]    dm_slave_rdata;

logic                       dm_master_req;
logic [CVA6Cfg.XLEN-1:0]    dm_master_add;
logic                       dm_master_we;
logic [CVA6Cfg.XLEN-1:0]    dm_master_wdata;
logic [CVA6Cfg.XLEN/8-1:0]  dm_master_be;
logic                       dm_master_gnt;
logic                       dm_master_r_valid;
logic [CVA6Cfg.XLEN-1:0]    dm_master_r_rdata;

// debug module
dm_top #(
    .NrHarts          ( 1                 ),
    .BusWidth         ( CVA6Cfg.XLEN      ),
    .SelectableHarts  ( 1'b1              ),
    .DmBaseAddress    ( 1'h0              ) // Map DM to addr 0
) i_dm_top (
    .clk_i            ( aclk              ),
    .rst_ni           ( aresetn           ), // PoR
    .testmode_i       ( test_en           ),
    .ndmreset_o       ( ndmreset          ),
    .dmactive_o       ( dmactive          ), // active debug session
    .debug_req_o      ( debug_req_irq     ),
    .unavailable_i    ( '0                ),
    .hartinfo_i       ( {ariane_pkg::DebugHartInfo} ),
    .slave_req_i      ( dm_slave_req      ),
    .slave_we_i       ( dm_slave_we       ),
    .slave_addr_i     ( dm_slave_addr     ),
    .slave_be_i       ( dm_slave_be       ),
    .slave_wdata_i    ( dm_slave_wdata    ),
    .slave_rdata_o    ( dm_slave_rdata    ),
    .master_req_o     ( dm_master_req     ),
    .master_add_o     ( dm_master_add     ),
    .master_we_o      ( dm_master_we      ),
    .master_wdata_o   ( dm_master_wdata   ),
    .master_be_o      ( dm_master_be      ),
    .master_gnt_i     ( dm_master_gnt     ),
    .master_r_valid_i ( dm_master_r_valid ),
    .master_r_rdata_i ( dm_master_r_rdata ),
    .dmi_rst_ni       ( aresetn           ),
    .dmi_req_valid_i  ( debug_req_valid   ),
    .dmi_req_ready_o  ( debug_req_ready   ),
    .dmi_req_i        ( debug_req         ),
    .dmi_resp_valid_o ( debug_resp_valid  ),
    .dmi_resp_ready_i ( debug_resp_ready  ),
    .dmi_resp_o       ( debug_resp        )
);

axi2mem #(
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH        ),
    .AXI_ADDR_WIDTH ( CVA6Cfg.XLEN        ),
    .AXI_DATA_WIDTH ( CVA6Cfg.XLEN        ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
) i_dm_axi2mem (
    .clk_i      ( aclk                      ),
    .rst_ni     ( aresetn                   ),
    .slave      ( slave_bus                 ),
    .req_o      ( dm_slave_req              ),
    .we_o       ( dm_slave_we               ),
    .addr_o     ( dm_slave_addr             ),
    .be_o       ( dm_slave_be               ),
    .data_o     ( dm_slave_wdata            ),
    .data_i     ( dm_slave_rdata            )
);

`ASSIGN_ARIANE_INTERFACE_FROM_XLNX_STYLE_INPUTS(s_axi_dmi_jtag,slave_bus)

logic [1:0]    axi_adapter_size;

assign axi_adapter_size = (CVA6Cfg.XLEN == 64) ? 2'b11 : 2'b10;

axi_adapter #(
    .CVA6Cfg               ( CVA6Cfg                  ),
    .DATA_WIDTH            ( CVA6Cfg.XLEN             ),
    .axi_req_t             ( ariane_axi::req_t        ),
    .axi_rsp_t             ( ariane_axi::resp_t       )
) i_dm_axi_master (
    .clk_i                 ( aclk                       ),
    .rst_ni                ( aresetn                     ),
    .req_i                 ( dm_master_req             ),
    .type_i                ( ariane_pkg::SINGLE_REQ    ),
    .amo_i                 ( ariane_pkg::AMO_NONE      ),
    .gnt_o                 ( dm_master_gnt             ),
    .addr_i                ( dm_master_add             ),
    .we_i                  ( dm_master_we              ),
    .wdata_i               ( dm_master_wdata           ),
    .be_i                  ( dm_master_be              ),
    .size_i                ( axi_adapter_size          ),
    .id_i                  ( '0                        ),
    .valid_o               ( dm_master_r_valid         ),
    .rdata_o               ( dm_master_r_rdata         ),
    .id_o                  (                           ),
    .critical_word_o       (                           ),
    .critical_word_valid_o (                           ),
    .axi_req_o             ( dm_axi_m_req              ),
    .axi_resp_i            ( dm_axi_m_resp             )
);

`AXI_ASSIGN_FROM_REQ(master_bus, dm_axi_m_req)
`AXI_ASSIGN_TO_RESP(dm_axi_m_resp, master_bus)
`ASSIGN_XLNX_INTERFACE_FROM_ARIANE_STYLE_INPUTS(m_axi_dmi_jtag, master_bus)
endmodule
