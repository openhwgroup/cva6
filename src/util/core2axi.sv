// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`define OKAY   2'b00
`define EXOKAY 2'b01
`define SLVERR 2'b10
`define DECERR 2'b11

module core2axi
#(
    parameter AXI4_ADDRESS_WIDTH = 32,
    parameter AXI4_DATA_WIDTH    = 32,
    parameter AXI4_ID_WIDTH      = 16,
    parameter AXI4_USER_WIDTH    = 10,
    parameter REGISTERED_GRANT   = "FALSE"           // "TRUE"|"FALSE"
)
(
    // Clock and Reset
    input logic                           clk_i,
    input logic                           rst_ni,

    input  logic                          data_req_i,
    output logic                          data_gnt_o,
    output logic                          data_rvalid_o,
    input  logic [AXI4_ADDRESS_WIDTH-1:0] data_addr_i,
    input  logic                          data_we_i,
    input  logic [3:0]                    data_be_i,
    output logic [31:0]                   data_rdata_o,
    input  logic [31:0]                   data_wdata_i,

    // ---------------------------------------------------------
    // AXI TARG Port Declarations ------------------------------
    // ---------------------------------------------------------
    //AXI write address bus -------------- // USED// -----------
    output logic [AXI4_ID_WIDTH-1:0]      aw_id_o,
    output logic [AXI4_ADDRESS_WIDTH-1:0] aw_addr_o,
    output logic [ 7:0]                   aw_len_o,
    output logic [ 2:0]                   aw_size_o,
    output logic [ 1:0]                   aw_burst_o,
    output logic                          aw_lock_o,
    output logic [ 3:0]                   aw_cache_o,
    output logic [ 2:0]                   aw_prot_o,
    output logic [ 3:0]                   aw_region_o,
    output logic [AXI4_USER_WIDTH-1:0]    aw_user_o,
    output logic [ 3:0]                   aw_qos_o,
    output logic                          aw_valid_o,
    input  logic                          aw_ready_i,
    // ---------------------------------------------------------

    //AXI write data bus -------------- // USED// --------------
    output logic [AXI4_DATA_WIDTH-1:0]    w_data_o,
    output logic [AXI4_DATA_WIDTH/8-1:0]  w_strb_o,
    output logic                          w_last_o,
    output logic [AXI4_USER_WIDTH-1:0]    w_user_o,
    output logic                          w_valid_o,
    input  logic                          w_ready_i,
    // ---------------------------------------------------------

    //AXI write response bus -------------- // USED// ----------
    input  logic   [AXI4_ID_WIDTH-1:0]    b_id_i,
    input  logic   [ 1:0]                 b_resp_i,
    input  logic                          b_valid_i,
    input  logic   [AXI4_USER_WIDTH-1:0]  b_user_i,
    output logic                          b_ready_o,
    // ---------------------------------------------------------

    //AXI read address bus -------------------------------------
    output logic [AXI4_ID_WIDTH-1:0]      ar_id_o,
    output logic [AXI4_ADDRESS_WIDTH-1:0] ar_addr_o,
    output logic [ 7:0]                   ar_len_o,
    output logic [ 2:0]                   ar_size_o,
    output logic [ 1:0]                   ar_burst_o,
    output logic                          ar_lock_o,
    output logic [ 3:0]                   ar_cache_o,
    output logic [ 2:0]                   ar_prot_o,
    output logic [ 3:0]                   ar_region_o,
    output logic [AXI4_USER_WIDTH-1:0]    ar_user_o,
    output logic [ 3:0]                   ar_qos_o,
    output logic                          ar_valid_o,
    input  logic                          ar_ready_i,
    // ---------------------------------------------------------

    //AXI read data bus ----------------------------------------
    input  logic [AXI4_ID_WIDTH-1:0]     r_id_i,
    input  logic [AXI4_DATA_WIDTH-1:0]   r_data_i,
    input  logic [ 1:0]                  r_resp_i,
    input  logic                         r_last_i,
    input  logic [AXI4_USER_WIDTH-1:0]   r_user_i,
    input  logic                         r_valid_i,
    output logic                         r_ready_o
    // ---------------------------------------------------------
  );


  enum logic [2:0] { IDLE, READ_WAIT, WRITE_DATA, WRITE_ADDR, WRITE_WAIT } CS, NS;

  logic [31:0]  rdata;
  logic         valid;
  logic         granted;

  // main FSM
  always_comb
  begin
    NS         = CS;
    granted    = 1'b0;
    valid      = 1'b0;

    aw_valid_o = 1'b0;
    ar_valid_o = 1'b0;
    r_ready_o  = 1'b0;
    w_valid_o  = 1'b0;
    b_ready_o  = 1'b0;

    case (CS)
      // wait for a request to come in from the core
      IDLE: begin
        // the same logic is also inserted in READ_WAIT and WRITE_WAIT, if you
        // change it here, take care to change it there too!
        if (data_req_i)
        begin
          // send address over aw channel for writes,
          // over ar channels for reads
          if (data_we_i)
          begin
            aw_valid_o = 1'b1;
            w_valid_o  = 1'b1;

            if (aw_ready_i) begin
              if (w_ready_i) begin
                granted = 1'b1;
                NS = WRITE_WAIT;
              end else begin
                NS = WRITE_DATA;
              end
            end else begin
              if (w_ready_i) begin
                NS = WRITE_ADDR;
              end else begin
                NS = IDLE;
              end
            end
          end else begin
            ar_valid_o = 1'b1;

            if (ar_ready_i) begin
              granted = 1'b1;
              NS = READ_WAIT;
            end else begin
              NS = IDLE;
            end
          end
        end else begin
          NS = IDLE;
        end
      end

      // if the bus has not accepted our write data right away, but has
      // accepted the address already
      WRITE_DATA: begin
        w_valid_o = 1'b1;
        if (w_ready_i) begin
          granted = 1'b1;
          NS = WRITE_WAIT;
        end
      end

      // the bus has accepted the write data, but not yet the address
      // this happens very seldom, but we still have to deal with the
      // situation
      WRITE_ADDR: begin
        aw_valid_o = 1'b1;

        if (aw_ready_i) begin
          granted = 1'b1;
          NS = WRITE_WAIT;
        end
      end

      // we have sent the address and data and just wait for the write data to
      // be done
      WRITE_WAIT:
      begin
        b_ready_o = 1'b1;

        if (b_valid_i)
        begin
          valid = 1'b1;

          NS = IDLE;
        end
      end

      // we wait for the read response, address has been sent successfully
      READ_WAIT:
      begin
        if (r_valid_i)
        begin
          valid     = 1'b1;
          r_ready_o = 1'b1;

          NS = IDLE;
        end
      end

      default:
      begin
        NS = IDLE;
      end
    endcase
  end

  // registers
  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if (~rst_ni)
    begin
      CS     <= IDLE;
    end
    else
    begin
      CS     <= NS;
    end
  end

  // take care of read data adaption
  generate if (AXI4_DATA_WIDTH == 32) begin
      assign rdata = r_data_i[31:0];
    end else if (AXI4_DATA_WIDTH == 64) begin
      logic [0:0] addr_q;

      always_ff @(posedge clk_i, negedge rst_ni)
      begin
        if (~rst_ni)
          addr_q <= '0;
        else
          if (data_gnt_o) // only update when we give the grant
            addr_q <= data_addr_i[2:2];
      end

      assign rdata = addr_q[0] ? r_data_i[63:32] : r_data_i[31:0];
    end else begin
      `ifndef SYNTHESIS
      initial $error("AXI4_WDATA_WIDTH has an invalid value");
      `endif
    end
  endgenerate;

  // take care of write data adaption
  generate
    genvar w;
    for(w = 0; w < AXI4_DATA_WIDTH/32; w++) begin
      assign w_data_o[w*32 + 31:w*32 + 0] = data_wdata_i; // just replicate the wdata to fill the bus
    end
  endgenerate

  // take care of write strobe
  generate if (AXI4_DATA_WIDTH == 32) begin
      assign w_strb_o = data_be_i;
    end else if (AXI4_DATA_WIDTH == 64) begin
      assign w_strb_o = data_addr_i[2] ? {data_be_i, 4'b0000} : {4'b0000, data_be_i};
    end else begin
      `ifndef SYNTHESIS
      initial $error("AXI4_DATA_WIDTH has an invalid value");
      `endif
    end
  endgenerate

  // AXI interface assignments
  assign aw_id_o     = '0;
  assign aw_addr_o   = data_addr_i;
  assign aw_size_o   = 3'b010;
  assign aw_len_o    = '0;
  assign aw_burst_o  = '0;
  assign aw_lock_o   = '0;
  assign aw_cache_o  = '0;
  assign aw_prot_o   = '0;
  assign aw_region_o = '0;
  assign aw_user_o   = '0;
  assign aw_qos_o    = '0;

  assign ar_id_o     = '0;
  assign ar_addr_o   = data_addr_i;
  assign ar_size_o   = 3'b010;
  assign ar_len_o    = '0;
  assign ar_burst_o  = '0;
  assign ar_prot_o   = '0;
  assign ar_region_o = '0;
  assign ar_lock_o   = '0;
  assign ar_cache_o  = '0;
  assign ar_qos_o    = '0;
  assign ar_user_o   = '0;

  assign w_last_o    = 1'b1;
  assign w_user_o    = '0;

  generate if (REGISTERED_GRANT == "TRUE")
    begin
      logic        valid_q;
      logic [31:0] rdata_q;

      always_ff @(posedge clk_i, negedge rst_ni)
      begin
        if (~rst_ni) begin
          valid_q <= 1'b0;
          rdata_q <= '0;
        end
        else
        begin
          valid_q <= valid;

          if (valid)
            rdata_q <= rdata;
        end
      end

      assign data_rdata_o  = rdata_q;
      assign data_rvalid_o = valid_q;
      assign data_gnt_o    = valid;
    end
    else
    begin
      assign data_rdata_o  = rdata;
      assign data_rvalid_o = valid;
      assign data_gnt_o    = granted;
    end
  endgenerate

endmodule
