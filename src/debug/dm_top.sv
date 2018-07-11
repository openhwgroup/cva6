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
    logic [NrHarts-1:0]               havereset;
    logic [NrHarts-1:0]               resumeack;
    logic [NrHarts-1:0]               haltreq;
    logic [NrHarts-1:0]               resumereq;
    logic [NrHarts-1:0]               ackhavereset;
    logic                             command_write;
    dm::command_t                     command;
    logic [NrHarts-1:0]               set_cmderror;
    dm::cmderr_t [NrHarts-1:0]        cmderror;
    logic [NrHarts-1:0]               cmdbusy;
    logic [dm::ProgBufSize-1:0][31:0] progbuf;
    logic [dm::DataCount-1:0][31:0]   data;

    dm_csrs #(
        .NrHarts(NrHarts)
    ) i_dm_csrs (
        .clk_i                ( clk_i                ),
        .rst_ni               ( rst_ni               ),
        .dmi_rst_ni           ( dmi_rst_ni           ),
        .dmi_req_valid_i      ( dmi_req_valid_i      ),
        .dmi_req_ready_o      ( dmi_req_ready_o      ),
        .dmi_req_bits_addr_i  ( dmi_req_bits_addr_i  ),
        .dmi_req_bits_op_i    ( dmi_req_bits_op_i    ),
        .dmi_req_bits_data_i  ( dmi_req_bits_data_i  ),
        .dmi_resp_valid_o     ( dmi_resp_valid_o     ),
        .dmi_resp_ready_i     ( dmi_resp_ready_i     ),
        .dmi_resp_bits_resp_o ( dmi_resp_bits_resp_o ),
        .dmi_resp_bits_data_o ( dmi_resp_bits_data_o ),
        .ndmreset_o           ( ndmreset_o           ),
        .dmactive_o           ( dmactive_o           ),
        .hartinfo_i           ( hartinfo             ),
        .halted_i             ( halted               ),
        .running_i            ( running              ),
        .unavailable_i        ( unavailable          ),
        .havereset_i          ( havereset            ),
        .resumeack_i          ( resumeack            ),
        .haltreq_o            ( haltreq              ),
        .resumereq_o          ( resumereq            ),
        .ackhavereset_o       ( ackhavereset         ),
        .command_write_o      ( command_write        ),
        .command_o            ( command              ),
        .set_cmderror_i       ( set_cmderror         ),
        .cmderror_i           ( cmderror             ),
        .cmdbusy_i            ( cmdbusy              ),
        .progbuf_o            ( progbuf              ),
        .data_o               ( data                 )
    );

    logic [NrHarts-1:0] ackhalt;
    // Debug Ctrl for each hart
    for (genvar i = 0; i < NrHarts; i++) begin : dm_hart_ctrl

        assign hartinfo[i] = ariane_pkg::DebugHartInfo;

        dm_ctrl i_dm_ctrl (
            .clk_i           ( clk_i            ),
            .dmactive_i      ( dmactive_o       ),
            .ndmreset_i      ( ndmreset_o       ),
            .debug_req_o     ( debug_req_o  [i] ),
            .halted_o        ( halted       [i] ),
            .running_o       ( running      [i] ),
            .unavailable_o   ( unavailable  [i] ),
            .havereset_o     ( havereset    [i] ),
            .resumeack_o     ( resumeack    [i] ),
            .haltreq_i       ( haltreq          ),
            .resumereq_i     ( resumereq        ),
            .ackhavereset_i  ( ackhavereset     ),
            .command_write_i ( command_write    ),
            .command_i       ( command          ),
            .set_cmderror_o  ( set_cmderror [i] ),
            .cmderror_o      ( cmderror     [i] ),
            .cmdbusy_o       ( cmdbusy      [i] ),
            .halted_i        ( ackhalt      [i] )
        );
    end

    logic        req;
    logic        we;
    logic [63:0] addr;
    logic [7:0]  be;
    logic [63:0] wdata;
    logic [63:0] rdata;
    logic [63:0] bit_en;

    dm_mem #(
        .NrHarts (NrHarts)
    ) i_dm_mem (
        .clk_i       ( clk_i     ),
        .dmactive_i  ( dmactive_o),
        .halted_o    ( ackhalt   ),
        .going_o     (           ),
        .resuming_o  (           ),
        .exception_o (           ),
        .progbuf_i   ( progbuf   ), // program buffer to expose
        .data_i      ( data      ),    // data in
        .req_i       ( req       ),
        .we_i        ( we        ),
        .addr_i      ( addr      ),
        .wdata_i     ( wdata     ),
        .be_i        ( be        ),
        .rdata_o     ( rdata     )
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
