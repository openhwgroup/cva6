// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Load Store Unit                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Load Store Unit, used to eliminate multiple access during  //
//                 processor stalls, and to align bytes and halfwords         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module riscv_load_store_unit
(
    input  logic         clk,
    input  logic         rst_n,

    // output to data memory
    output logic         data_req_o,
    input  logic         data_gnt_i,
    input  logic         data_rvalid_i,
    input  logic         data_err_i,

    output logic [31:0]  data_addr_o,
    output logic         data_we_o,
    output logic [3:0]   data_be_o,
    output logic [31:0]  data_wdata_o,
    input  logic [31:0]  data_rdata_i,

    // signals from ex stage
    input  logic         data_we_ex_i,         // write enable                      -> from ex stage
    input  logic [1:0]   data_type_ex_i,       // Data type word, halfword, byte    -> from ex stage
    input  logic [31:0]  data_wdata_ex_i,      // data to write to memory           -> from ex stage
    input  logic [1:0]   data_reg_offset_ex_i, // offset inside register for stores -> from ex stage
    input  logic [1:0]   data_sign_ext_ex_i,   // sign extension                    -> from ex stage

    output logic [31:0]  data_rdata_ex_o,      // requested data                    -> to ex stage
    input  logic         data_req_ex_i,        // data request                      -> from ex stage
    input  logic [31:0]  operand_a_ex_i,       // operand a from RF for address     -> from ex stage
    input  logic [31:0]  operand_b_ex_i,       // operand b from RF for address     -> from ex stage
    input  logic         addr_useincr_ex_i,    // use a + b or just a for address   -> from ex stage

    input  logic         data_misaligned_ex_i, // misaligned access in last ld/st   -> from ID/EX pipeline
    output logic         data_misaligned_o,    // misaligned access was detected    -> to controller

    // stall signal
    output logic         lsu_ready_ex_o, // LSU ready for new data in EX stage
    output logic         lsu_ready_wb_o, // LSU ready for new data in WB stage

    input  logic         ex_valid_i,
    output logic         busy_o
);

  logic [31:0]  data_addr_int;

  // registers for data_rdata alignment and sign extension
  logic [1:0]   data_type_q;
  logic [1:0]   rdata_offset_q;
  logic [1:0]   data_sign_ext_q;
  logic         data_we_q;

  logic [1:0]   wdata_offset;   // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [31:0]  data_wdata;

  logic         misaligned_st;   // high if we are currently performing the second part of a misaligned store


  enum logic [1:0]  { IDLE, WAIT_RVALID, WAIT_RVALID_EX_STALL, IDLE_EX_STALL } CS, NS;

  logic [31:0]  rdata_q;

  ///////////////////////////////// BE generation ////////////////////////////////
  always_comb
  begin
    case (data_type_ex_i) // Data type 00 Word, 01 Half word, 11,10 byte
      2'b00:
      begin // Writing a word
        if (misaligned_st == 1'b0)
        begin // non-misaligned case
          case (data_addr_int[1:0])
            2'b00: data_be = 4'b1111;
            2'b01: data_be = 4'b1110;
            2'b10: data_be = 4'b1100;
            2'b11: data_be = 4'b1000;
          endcase; // case (data_addr_int[1:0])
        end
        else
        begin // misaligned case
          case (data_addr_int[1:0])
            2'b00: data_be = 4'b0000; // this is not used, but included for completeness
            2'b01: data_be = 4'b0001;
            2'b10: data_be = 4'b0011;
            2'b11: data_be = 4'b0111;
          endcase; // case (data_addr_int[1:0])
        end
      end

      2'b01:
      begin // Writing a half word
        if (misaligned_st == 1'b0)
        begin // non-misaligned case
          case (data_addr_int[1:0])
            2'b00: data_be = 4'b0011;
            2'b01: data_be = 4'b0110;
            2'b10: data_be = 4'b1100;
            2'b11: data_be = 4'b1000;
          endcase; // case (data_addr_int[1:0])
        end
        else
        begin // misaligned case
          data_be = 4'b0001;
        end
      end

      2'b10,
      2'b11: begin // Writing a byte
        case (data_addr_int[1:0])
          2'b00: data_be = 4'b0001;
          2'b01: data_be = 4'b0010;
          2'b10: data_be = 4'b0100;
          2'b11: data_be = 4'b1000;
        endcase; // case (data_addr_int[1:0])
      end
    endcase; // case (data_type_ex_i)
  end

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses and
  // register offsets here
  assign wdata_offset = data_addr_int[1:0] - data_reg_offset_ex_i[1:0];
  always_comb
  begin
    case (wdata_offset)
      2'b00: data_wdata = data_wdata_ex_i[31:0];
      2'b01: data_wdata = {data_wdata_ex_i[23:0], data_wdata_ex_i[31:24]};
      2'b10: data_wdata = {data_wdata_ex_i[15:0], data_wdata_ex_i[31:16]};
      2'b11: data_wdata = {data_wdata_ex_i[ 7:0], data_wdata_ex_i[31: 8]};
    endcase; // case (wdata_offset)
  end


  // FF for rdata alignment and sign-extension
  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      data_type_q     <= '0;
      rdata_offset_q  <= '0;
      data_sign_ext_q <= '0;
      data_we_q       <= 1'b0;
    end
    else if (data_gnt_i == 1'b1) // request was granted, we wait for rvalid and can continue to WB
    begin
      data_type_q     <= data_type_ex_i;
      rdata_offset_q  <= data_addr_int[1:0];
      data_sign_ext_q <= data_sign_ext_ex_i;
      data_we_q       <= data_we_ex_i;
    end
  end


  ////////////////////////////////////////////////////////////////////////
  //  ____  _               _____      _                 _              //
  // / ___|(_) __ _ _ __   | ____|_  _| |_ ___ _ __  ___(_) ___  _ __   //
  // \___ \| |/ _` | '_ \  |  _| \ \/ / __/ _ \ '_ \/ __| |/ _ \| '_ \  //
  //  ___) | | (_| | | | | | |___ >  <| ||  __/ | | \__ \ | (_) | | | | //
  // |____/|_|\__, |_| |_| |_____/_/\_\\__\___|_| |_|___/_|\___/|_| |_| //
  //          |___/                                                     //
  ////////////////////////////////////////////////////////////////////////

  logic [31:0] data_rdata_ext;

  logic [31:0] rdata_w_ext; // sign extension for words, actually only misaligned assembly
  logic [31:0] rdata_h_ext; // sign extension for half words
  logic [31:0] rdata_b_ext; // sign extension for bytes

  // take care of misaligned words
  always_comb
  begin
    case (rdata_offset_q)
      2'b00: rdata_w_ext = data_rdata_i[31:0];
      2'b01: rdata_w_ext = {data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10: rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
      2'b11: rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
    endcase
  end

  // sign extension for half words
  always_comb
  begin
    case (rdata_offset_q)
      2'b00:
      begin
        if (data_sign_ext_q == 2'b00)
          rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
        else if (data_sign_ext_q == 2'b10)
          rdata_h_ext = {16'hffff, data_rdata_i[15:0]};
        else
          rdata_h_ext = {{16{data_rdata_i[15]}}, data_rdata_i[15:0]};
      end

      2'b01:
      begin
        if (data_sign_ext_q == 2'b00)
          rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
        else if (data_sign_ext_q == 2'b10)
          rdata_h_ext = {16'hffff, data_rdata_i[23:8]};
        else
          rdata_h_ext = {{16{data_rdata_i[23]}}, data_rdata_i[23:8]};
      end

      2'b10:
      begin
        if (data_sign_ext_q == 2'b00)
          rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
        else if (data_sign_ext_q == 2'b10)
          rdata_h_ext = {16'hffff, data_rdata_i[31:16]};
        else
          rdata_h_ext = {{16{data_rdata_i[31]}}, data_rdata_i[31:16]};
      end

      2'b11:
      begin
        if (data_sign_ext_q == 2'b00)
          rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
        else if (data_sign_ext_q == 2'b10)
          rdata_h_ext = {16'hffff, data_rdata_i[7:0], rdata_q[31:24]};
        else
          rdata_h_ext = {{16{data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
      end
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb
  begin
    case (rdata_offset_q)
      2'b00:
      begin
        if (data_sign_ext_q == 2'b00)
          rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
        else if (data_sign_ext_q == 2'b10)
          rdata_b_ext = {24'hff_ffff, data_rdata_i[7:0]};
        else
          rdata_b_ext = {{24{data_rdata_i[7]}}, data_rdata_i[7:0]};
      end

      2'b01: begin
        if (data_sign_ext_q == 2'b00)
          rdata_b_ext = {24'h00_0000, data_rdata_i[15:8]};
        else if (data_sign_ext_q == 2'b10)
          rdata_b_ext = {24'hff_ffff, data_rdata_i[15:8]};
        else
          rdata_b_ext = {{24{data_rdata_i[15]}}, data_rdata_i[15:8]};
      end

      2'b10:
      begin
        if (data_sign_ext_q == 2'b00)
          rdata_b_ext = {24'h00_0000, data_rdata_i[23:16]};
        else if (data_sign_ext_q == 2'b10)
          rdata_b_ext = {24'hff_ffff, data_rdata_i[23:16]};
        else
          rdata_b_ext = {{24{data_rdata_i[23]}}, data_rdata_i[23:16]};
      end

      2'b11:
      begin
        if (data_sign_ext_q == 2'b00)
          rdata_b_ext = {24'h00_0000, data_rdata_i[31:24]};
        else if (data_sign_ext_q == 2'b10)
          rdata_b_ext = {24'hff_ffff, data_rdata_i[31:24]};
        else
          rdata_b_ext = {{24{data_rdata_i[31]}}, data_rdata_i[31:24]};
      end
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb
  begin
    case (data_type_q)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = rdata_h_ext;
      2'b10,2'b11: data_rdata_ext = rdata_b_ext;
    endcase //~case(rdata_type_q)
  end



  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      CS            <= IDLE;
      rdata_q       <= '0;
    end
    else
    begin
      CS            <= NS;

      if (data_rvalid_i && (~data_we_q))
      begin
        // if we have detected a misaligned access, and we are
        // currently doing the first part of this access, then
        // store the data coming from memory in rdata_q.
        // In all other cases, rdata_q gets the value that we are
        // writing to the register file
        if ((data_misaligned_ex_i == 1'b1) || (data_misaligned_o == 1'b1))
          rdata_q  <= data_rdata_i;
        else
          rdata_q  <= data_rdata_ext;
      end
    end
  end

  // output to register file
  assign data_rdata_ex_o = (data_rvalid_i == 1'b1) ? data_rdata_ext : rdata_q;

  // output to data interface
  assign data_addr_o   = data_addr_int;
  assign data_wdata_o  = data_wdata;
  assign data_we_o     = data_we_ex_i;
  assign data_be_o     = data_be;

  assign misaligned_st = data_misaligned_ex_i;

  // FSM
  always_comb
  begin
    NS             = CS;

    data_req_o     = 1'b0;

    lsu_ready_ex_o = 1'b1;
    lsu_ready_wb_o = 1'b1;

    case(CS)
      // starts from not active and stays in IDLE until request was granted
      IDLE:
      begin
        data_req_o = data_req_ex_i;

        if(data_req_ex_i) begin
          lsu_ready_ex_o = 1'b0;

          if(data_gnt_i) begin
            lsu_ready_ex_o = 1'b1;

            if (ex_valid_i)
              NS = WAIT_RVALID;
            else
              NS = WAIT_RVALID_EX_STALL;
          end

          if(data_err_i) begin
            lsu_ready_ex_o = 1'b1;
          end

        end
      end //~ IDLE

      // wait for rvalid in WB stage and send a new request if there is any
      WAIT_RVALID:
      begin
        lsu_ready_wb_o = 1'b0;

        if (data_rvalid_i) begin
          // we don't have to wait for anything here as we are the only stall
          // source for the WB stage
          lsu_ready_wb_o = 1'b1;

          data_req_o = data_req_ex_i;

          if (data_req_ex_i) begin
            lsu_ready_ex_o = 1'b0;

            if (data_gnt_i) begin
              lsu_ready_ex_o = 1'b1;

              if(ex_valid_i)
                NS = WAIT_RVALID;
              else
                NS = WAIT_RVALID_EX_STALL;
            end else begin
              if(data_err_i) begin
                lsu_ready_ex_o = 1'b1;
              end
              NS = IDLE;
            end
          end else begin
            if (data_rvalid_i) begin
              // no request, so go to IDLE
              NS = IDLE;
            end
          end
        end
      end

      // wait for rvalid while still in EX stage
      // we end up here when there was an EX stall, so in this cycle we just
      // wait and don't send new requests
      WAIT_RVALID_EX_STALL:
      begin
        data_req_o = 1'b0;

        if (data_rvalid_i) begin
          if (ex_valid_i) begin
            // we are done and can go back to idle
            // the data is safely stored already
            NS = IDLE;
          end else begin
            // we have to wait until ex_stall is deasserted
            NS = IDLE_EX_STALL;
          end
        end else begin
          // we didn't yet receive the rvalid, so we check the ex_stall
          // signal. If we are no longer stalled we can change to the "normal"
          // WAIT_RVALID state
          if (ex_valid_i)
            NS = WAIT_RVALID;
        end
      end

      IDLE_EX_STALL:
      begin
        // wait for us to be unstalled and then change back to IDLE state
        if (ex_valid_i) begin
          NS = IDLE;
        end
      end

      default: begin
        NS = IDLE;
      end
    endcase
  end

  // check for misaligned accesses that need a second memory access
  // If one is detected, this is signaled with data_misaligned_o to
  // the controller which selectively stalls the pipeline
  always_comb
  begin
    data_misaligned_o = 1'b0;

    if((data_req_ex_i == 1'b1) && (data_misaligned_ex_i == 1'b0))
    begin
      case (data_type_ex_i)
        2'b00: // word
        begin
          if(data_addr_int[1:0] != 2'b00)
            data_misaligned_o = 1'b1;
        end
        2'b01: // half word
        begin
          if(data_addr_int[1:0] == 2'b11)
            data_misaligned_o = 1'b1;
        end
      endcase // case (data_type_ex_i)
    end
  end

  // generate address from operands
  assign data_addr_int = (addr_useincr_ex_i) ? (operand_a_ex_i + operand_b_ex_i) : operand_a_ex_i;

  assign busy_o = (CS == WAIT_RVALID) || (CS == WAIT_RVALID_EX_STALL) || (CS == IDLE_EX_STALL) || (data_req_o == 1'b1);


  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

  `ifndef VERILATOR
    // make sure there is no new request when the old one is not yet completely done
    assert property (
      @(posedge clk) ((CS == WAIT_RVALID) && (data_gnt_i == 1'b1)) |-> (data_rvalid_i == 1'b1) ) else $display("It should not be possible to get a grand without an rvalid for the last request %t", $time);

    assert property (
      @(posedge clk) (CS == IDLE) |-> (data_rvalid_i == 1'b0) ) else $display("There should be no rvalid when we the LSU is IDLE %t", $time);

    // assert that the address does not contain X when request is sent
    assert property ( @(posedge clk) (data_req_o) |-> (!$isunknown(data_addr_o)) ) else $display("There has been a data request but the address is unknown %t", $time);
  `endif
endmodule
