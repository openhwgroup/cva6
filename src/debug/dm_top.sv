/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_top.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2018
 *
 * Description: Top-level of debug module (DM). This is an AXI-Slave.
 *              DTM protocol is equal to SiFives debug protocol to leverage
 *              SW infrastructure re-use. As of version 0.13
 */

module dm_top #(
    parameter int NrHarts      = -1,
    parameter int AxiIdWidth   = -1,
    parameter int AxiAddrWidth = -1,
    parameter int AxiDataWidth = -1,
    parameter int AxiUserWidth = -1
)(
    input  logic               clk_i,       // clock
    input  logic               rst_ni,      // asynchronous reset active low, connect PoR here, not the system reset
    output logic               ndmreset_o,  // non-debug module reset
    output logic               dmactive_o,  // debug module is active
    output logic [NrHarts-1:0] debug_req_o, // async debug request

    AXI_BUS.Slave              axi_slave,   // bus slave, for an execution based technique
    // Connection to DTM - compatible to RocketChip Debug Module
    input  logic               dmi_rst_ni,
    input  logic               dmi_req_valid_i,
    output logic               dmi_req_ready_o,
    input  logic [ 6:0]        dmi_req_bits_addr_i,
    input  logic [ 1:0]        dmi_req_bits_op_i, // 0 = nop, 1 = read, 2 = write
    input  logic [31:0]        dmi_req_bits_data_i,

    output logic               dmi_resp_valid_o,
    input  logic               dmi_resp_ready_i,
    output logic [ 1:0]        dmi_resp_bits_resp_o,
    output logic [31:0]        dmi_resp_bits_data_o
);

    // Debug CSRs
    dm::hartinfo_t [NrHarts-1:0]      hartinfo;
    logic [NrHarts-1:0]               halted;
    logic [NrHarts-1:0]               running;
    logic [NrHarts-1:0]               unavailable;
    logic [NrHarts-1:0]               resumeack;
    logic [NrHarts-1:0]               haltreq;
    logic [NrHarts-1:0]               resumereq;
    logic                             cmd_valid;
    dm::command_t                     cmd;

    logic [NrHarts-1:0]               cmderror_valid;
    dm::cmderr_t [NrHarts-1:0]        cmderror;
    logic [NrHarts-1:0]               cmdbusy;
    logic [dm::ProgBufSize-1:0][31:0] progbuf;
    logic [dm::DataCount-1:0][31:0]   data_csrs_mem;
    logic [dm::DataCount-1:0][31:0]   data_mem_csrs;
    logic                             data_valid;
    logic [19:0]                      hartsel;

    dm_csrs #(
        .NrHarts(NrHarts)
    ) i_dm_csrs (
        .clk_i                   ( clk_i                ),
        .rst_ni                  ( rst_ni               ),
        .dmi_rst_ni              ( dmi_rst_ni           ),
        .dmi_req_valid_i         ( dmi_req_valid_i      ),
        .dmi_req_ready_o         ( dmi_req_ready_o      ),
        .dmi_req_bits_addr_i     ( dmi_req_bits_addr_i  ),
        .dmi_req_bits_op_i       ( dmi_req_bits_op_i    ),
        .dmi_req_bits_data_i     ( dmi_req_bits_data_i  ),
        .dmi_resp_valid_o        ( dmi_resp_valid_o     ),
        .dmi_resp_ready_i        ( dmi_resp_ready_i     ),
        .dmi_resp_bits_resp_o    ( dmi_resp_bits_resp_o ),
        .dmi_resp_bits_data_o    ( dmi_resp_bits_data_o ),
        .ndmreset_o              ( ndmreset_o           ),
        .dmactive_o              ( dmactive_o           ),
        .hartsel_o               ( hartsel              ),
        .hartinfo_i              ( hartinfo             ),
        .halted_i                ( halted               ),
        .unavailable_i           ( unavailable          ),
        .resumeack_i             ( resumeack            ),
        .haltreq_o               ( haltreq              ),
        .resumereq_o             ( resumereq            ),
        .cmd_valid_o             ( cmd_valid            ),
        .cmd_o                   ( cmd                  ),
        .cmderror_valid_i        ( cmderror_valid       ),
        .cmderror_i              ( cmderror             ),
        .cmdbusy_i               ( cmdbusy              ),
        .progbuf_o               ( progbuf              ),
        .data_i                  ( data_mem_csrs        ),
        .data_valid_i            ( data_valid           ),
        .data_o                  ( data_csrs_mem        ),
        .sbaddress_o             (                      ),
        .sbaddress_write_valid_o (                      ),
        .sbreadonaddr_o          (                      ),
        .sbautoincrement_o       (                      ),
        .sbaccess_o              (                      ),
        .sbdata_o                (                      ),
        .sbdata_read_valid_o     (                      ),
        .sbdata_write_valid_o    (                      ),
        .sbdata_i                ( '0                   ),
        .sbdata_valid_i          ( '0                   ),
        .sbbusy_i                ( '0                   ),
        .sberror_i               ( '0                   ),
        .sberror_valid_i         ( '0                   )
    );

    assign unavailable = '0;

    // Debug Ctrl for each hart
    for (genvar i = 0; i < NrHarts; i++) begin : dm_hart_ctrl
        assign hartinfo[i] = ariane_pkg::DebugHartInfo;
    end

    logic        req;
    logic        we;
    logic [63:0] addr;
    logic [7:0]  be;
    logic [63:0] wdata;
    logic [63:0] rdata;

    dm_mem #(
        .NrHarts (NrHarts)
    ) i_dm_mem (
        .clk_i            ( clk_i           ),
        .dmactive_i       ( dmactive_o      ),
        .debug_req_o      ( debug_req_o     ),
        .hartsel_i        ( hartsel         ),

        .haltreq_i        ( haltreq         ),
        .resumereq_i      ( resumereq       ),
        .halted_o         ( halted          ),
        .resuming_o       ( resumeack       ),
        .cmd_valid_i      ( cmd_valid       ),
        .cmd_i            ( cmd             ),
        .cmderror_valid_o ( cmderror_valid  ),
        .cmderror_o       ( cmderror        ),
        .cmdbusy_o        ( cmdbusy         ),

        .progbuf_i        ( progbuf         ),
        .data_i           ( data_csrs_mem   ),
        .data_o           ( data_mem_csrs   ),
        .data_valid_o     ( data_valid      ),

        .req_i            ( req             ),
        .we_i             ( we              ),
        .addr_i           ( addr            ),
        .wdata_i          ( wdata           ),
        .be_i             ( be              ),
        .rdata_o          ( rdata           )
    );

    axi2mem #(
        .AXI_ID_WIDTH   ( AxiIdWidth   ),
        .AXI_ADDR_WIDTH ( AxiAddrWidth ),
        .AXI_DATA_WIDTH ( AxiDataWidth ),
        .AXI_USER_WIDTH ( AxiUserWidth )
    ) i_axi2mem (
        .clk_i  ( clk_i      ),
        .rst_ni ( dmactive_o ),
        .slave  ( axi_slave  ),
        .req_o  ( req        ),
        .we_o   ( we         ),
        .addr_o ( addr       ),
        .be_o   ( be         ),
        .data_o ( wdata      ),
        .data_i ( rdata      )
    );
endmodule
