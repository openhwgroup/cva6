// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 17/07/2017
// Description: AXI Lite compatible interface
//

module axi_lite_interface #(
    parameter int unsigned AXI_ADDR_WIDTH = 64,
    parameter int unsigned AXI_DATA_WIDTH = 64,
    parameter int unsigned AXI_ID_WIDTH   = 10
)(
    input logic                       clk_i,    // Clock
    input logic                       rst_ni,  // Asynchronous reset active low

    AXI_BUS.Slave                     slave,

    output logic [AXI_ADDR_WIDTH-1:0] address_o,
    output logic                      en_o,        // transaction is valid
    output logic                      we_o,        // write
    input  logic [AXI_DATA_WIDTH-1:0] data_i,      // data
    output logic [AXI_DATA_WIDTH-1:0] data_o
);

    // The RLAST signal is not required, and is considered asserted for every transfer on the read data channel.
    enum logic [1:0] { IDLE, READ, WRITE, WRITE_B} CS, NS;
    // save the trans id, we will need it for reflection otherwise we are not plug compatible to the AXI standard
    logic [AXI_ID_WIDTH-1:0]   trans_id_n, trans_id_q;
    // address register
    logic [AXI_ADDR_WIDTH-1:0] address_n,  address_q;

    // pass through read data on the read data channel
    assign slave.r_data = data_i;
    // send back the transaction id we've latched
    assign slave.r_id = trans_id_q;
    assign slave.b_id = trans_id_q;
    // set r_last to one as defined by the AXI4 - Lite standard
    assign slave.r_last = 1'b1;
    // we do not support any errors so set response flag to all zeros
    assign slave.b_resp = 2'b0;
    assign slave.r_resp = 2'b0;
    // output data which we want to write to the slave
    assign data_o = slave.w_data;
    // ------------------------
    // AXI4-Lite State Machine
    // ------------------------
    always_comb begin
        // default signal assignment
        NS         = CS;
        address_n  = address_q;
        trans_id_n = trans_id_q;

        // we'll answer a write request only if we got address and data
        slave.aw_ready = 1'b0;
        slave.w_ready  = 1'b0;
        slave.b_valid  = 1'b0;

        slave.ar_ready = 1'b1;
        slave.r_valid  = 1'b0;

        address_o      = '0;
        we_o           = 1'b0;
        en_o           = 1'b0;

        case (CS)
            // we are ready to accept a new request
            IDLE: begin
                // we've git a valid write request, we also know that we have asserted the aw_ready
                if (slave.aw_valid) begin

                    slave.aw_ready = 1'b1;
                    // this costs performance but the interconnect does not obey the AXI standard
                    NS = WRITE;
                    // save address
                    address_n = slave.aw_addr;
                    // save the transaction id for reflection
                    trans_id_n = slave.aw_id;

                // we've got a valid read request, we also know that we have asserted the ar_ready
                end else if (slave.ar_valid) begin
                    NS = READ;
                    address_n = slave.ar_addr;
                    // also request the word from the memory-like interface
                    address_o = slave.ar_addr;
                    // save the transaction id for reflection
                    trans_id_n = slave.ar_id;

                end
            end
            // We've got a read request at least one cycle earlier
            // so data_i will already contain the data we'd like tor read
            READ: begin
                // enable the ram-like
                en_o       = 1'b1;
                // we are not ready for another request here
                slave.ar_ready = 1'b0;
                // further assert the correct address
                address_o = address_q;
                // the read is valid
                slave.r_valid = 1'b1;
                // check if we got a valid r_ready and go back to IDLE
                if (slave.r_ready)
                    NS = IDLE;
            end
            // We've got a write request at least one cycle earlier
            // wait here for the data
            WRITE: begin
                if (slave.w_valid) begin
                    // we are not ready for another request here
                    slave.ar_ready = 1'b0;
                    slave.w_ready = 1'b1;
                    // use the latched address
                    address_o = address_q;
                    en_o = 1'b1;
                    we_o = 1'b1;
                    // close this request
                    NS = WRITE_B;
                end
            end

            WRITE_B: begin
                slave.b_valid  = 1'b1;
                // we've already performed the write here so wait for the ready signal
                if (slave.b_ready)
                    NS = IDLE;
            end
            default:;

        endcase
    end

    // ------------------------
    // Registers
    // ------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            CS         <= IDLE;
            address_q  <= '0;
            trans_id_q <= '0;
        end else begin
            CS         <= NS;
            address_q  <= address_n;
            trans_id_q <= trans_id_n;
        end
    end

    // ------------------------
    // Assertions
    // ------------------------
    // Listen for illegal transactions
    `ifndef SYNTHESIS
    `ifndef VERILATOR
        // check that burst length is just one
        assert property (@(posedge clk_i) slave.ar_valid |->  ((slave.ar_len == 8'b0) && (slave.ar_size == $clog2(AXI_ADDR_WIDTH/8))))
        else begin $error("AXI Lite does not support bursts larger than 1 or byte length unequal to the native bus size"); $stop(); end
        // do the same for the write channel
        assert property (@(posedge clk_i) slave.aw_valid |->  ((slave.aw_len == 8'b0) && (slave.aw_size == $clog2(AXI_ADDR_WIDTH/8))))
        else begin $error("AXI Lite does not support bursts larger than 1 or byte length unequal to the native bus size"); $stop(); end
    `endif
    `endif
endmodule
