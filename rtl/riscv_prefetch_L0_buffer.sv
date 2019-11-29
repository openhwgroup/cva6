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
// Design Name:    Prefetcher Buffer for 128 bit memory interface             //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module riscv_prefetch_L0_buffer
#(
  parameter                                   RDATA_IN_WIDTH = 128
)
(
  input  logic                                clk,
  input  logic                                rst_n,

  input  logic                                req_i,

  input  logic                                branch_i,
  input  logic [31:0]                         addr_i,

  input  logic                                hwloop_i,
  input  logic [31:0]                         hwloop_target_i,

  input  logic                                ready_i,
  output logic                                valid_o,
  output logic [31:0]                         rdata_o,
  output logic [31:0]                         addr_o,
  output logic                                is_hwlp_o, // is set when the currently served data is from a hwloop

  // goes to instruction memory / instruction cache
  output logic                                instr_req_o,
  output logic [31:0]                         instr_addr_o,
  input  logic                                instr_gnt_i,
  input  logic                                instr_rvalid_i,
  input  logic [RDATA_IN_WIDTH/32-1:0][31:0]  instr_rdata_i,

  // Prefetch Buffer Status
  output logic                                busy_o
);

  logic                               busy_L0;

  enum logic [3:0] { IDLE, BRANCHED,
                     HWLP_WAIT_GNT, HWLP_GRANTED, HWLP_GRANTED_WAIT, HWLP_FETCH_DONE,
                     NOT_VALID, NOT_VALID_GRANTED, NOT_VALID_CROSS, NOT_VALID_CROSS_GRANTED,
                     VALID, VALID_CROSS, VALID_GRANTED, VALID_FETCH_DONE } CS, NS;

  logic                               do_fetch;
  logic                               do_hwlp, do_hwlp_int;
  logic                               use_last;
  logic                               save_rdata_last;
  logic                               use_hwlp;
  logic                               save_rdata_hwlp;
  logic                               valid;

  logic                               hwlp_is_crossword;
  logic                               is_crossword;
  logic                               next_is_crossword;
  logic                               next_valid;
  logic                               next_upper_compressed;
  logic                               fetch_possible;
  logic                               upper_is_compressed;

  logic                       [31:0]  addr_q, addr_n, addr_int, addr_aligned_next, addr_real_next;
  logic                               is_hwlp_q, is_hwlp_n;

  logic                       [31:0]  rdata_last_q;

  logic                               valid_L0;
  logic [RDATA_IN_WIDTH/32-1:0][31:0] rdata_L0;
  logic                        [31:0] addr_L0;

  logic                               fetch_valid;
  logic                               fetch_gnt;

  // prepared data for output
  logic                        [31:0] rdata, rdata_unaligned;

  logic                               aligned_is_compressed, unaligned_is_compressed;
  logic                               hwlp_aligned_is_compressed, hwlp_unaligned_is_compressed;


  riscv_L0_buffer
  #(
    .RDATA_IN_WIDTH ( RDATA_IN_WIDTH )
  )
  L0_buffer_i
  (
    .clk                  ( clk                ),
    .rst_n                ( rst_n              ),

    .prefetch_i           ( do_fetch           ),
    .prefetch_addr_i      ( addr_real_next   ), //addr_aligned_next

    .branch_i             ( branch_i           ),
    .branch_addr_i        ( addr_i             ),

    .hwlp_i               ( do_hwlp | do_hwlp_int ),
    .hwlp_addr_i          ( hwloop_target_i    ),

    .fetch_gnt_o          ( fetch_gnt          ),
    .fetch_valid_o        ( fetch_valid        ),

    .valid_o              ( valid_L0           ),
    .rdata_o              ( rdata_L0           ),
    .addr_o               ( addr_L0            ),

    .instr_req_o          ( instr_req_o        ),
    .instr_addr_o         ( instr_addr_o       ),
    .instr_gnt_i          ( instr_gnt_i        ),
    .instr_rvalid_i       ( instr_rvalid_i     ),
    .instr_rdata_i        ( instr_rdata_i      ),

    .busy_o               ( busy_L0            )
  );


  assign rdata = (use_last || use_hwlp) ? rdata_last_q : rdata_L0[addr_o[3:2]];

  // the lower part of rdata_unaligned is always the higher part of rdata
  assign rdata_unaligned[15:0] = rdata[31:16];

  always_comb
  begin
    // rdata_unaligned[31:16] = '0; Not Needed

    case(addr_o[3:2])
       2'b00: begin rdata_unaligned[31:16] = rdata_L0[1][15:0]; end
       2'b01: begin rdata_unaligned[31:16] = rdata_L0[2][15:0]; end
       2'b10: begin rdata_unaligned[31:16] = rdata_L0[3][15:0]; end
       2'b11: begin rdata_unaligned[31:16] = rdata_L0[0][15:0]; end
    endcase // addr_o
  end


  assign unaligned_is_compressed = rdata[17:16] != 2'b11;
  assign aligned_is_compressed   = rdata[1:0] != 2'b11;
  assign upper_is_compressed     = rdata_L0[3][17:16] != 2'b11;
  assign is_crossword            = (addr_o[3:1] == 3'b111) && (~upper_is_compressed);
  assign next_is_crossword       = ((addr_o[3:1] == 3'b110) && (aligned_is_compressed) && (~upper_is_compressed)) || ((addr_o[3:1] == 3'b101) && (~unaligned_is_compressed) && (~upper_is_compressed));
  assign next_upper_compressed   = ((addr_o[3:1] == 3'b110) && (aligned_is_compressed) && upper_is_compressed) || ((addr_o[3:1] == 3'b101) && (~unaligned_is_compressed) && upper_is_compressed);
  assign next_valid              = ((addr_o[3:2] != 2'b11) || next_upper_compressed) && (~next_is_crossword) && valid;

  //addr_o[3:2] == 2'b11;// ((addr_o[3:1] == 3'b101) & (~upper_is_compressed)) | addr_o[3:2] == 2'b11; //
  assign fetch_possible          =  (addr_o[3:2] == 2'b11 );

  assign addr_aligned_next = { addr_o[31:2], 2'b00 } + 32'h4;
  assign addr_real_next    = (next_is_crossword) ? { addr_o[31:4], 4'b0000 } + 32'h16 : { addr_o[31:2], 2'b00 } + 32'h4;

  assign hwlp_unaligned_is_compressed = rdata_L0[2][17:16] != 2'b11;
  assign hwlp_aligned_is_compressed   = rdata_L0[3][1:0] != 2'b11;
  assign hwlp_is_crossword            = (hwloop_target_i[3:1] == 3'b111) && (~upper_is_compressed);

  always_comb
  begin
    addr_int    = addr_o;

    // advance address when pipeline is unstalled
    if (ready_i) begin

      if (addr_o[1]) begin
        // unaligned case
        // always move to next entry in the FIFO

        if (unaligned_is_compressed) begin
          addr_int = { addr_aligned_next[31:2], 2'b00};
        end else begin
          addr_int = { addr_aligned_next[31:2], 2'b10};
        end

      end else begin
        // aligned case

        if (aligned_is_compressed) begin
          // just increase address, do not move to next entry in the FIFO
          addr_int = { addr_o[31:2], 2'b10 };
        end else begin
          // move to next entry in the FIFO
          addr_int = { addr_aligned_next[31:2], 2'b00 };
        end
      end

    end
  end

  always_comb
  begin
    NS              = CS;
    do_fetch        = 1'b0;
    do_hwlp         = 1'b0;
    do_hwlp_int     = 1'b0;
    use_last        = 1'b0;
    use_hwlp        = 1'b0;
    save_rdata_last = 1'b0;
    save_rdata_hwlp = 1'b0;
    valid           = 1'b0;
    addr_n          = addr_int;
    is_hwlp_n       = is_hwlp_q;

    if (ready_i)
      is_hwlp_n = 1'b0;

    case (CS)
      IDLE: begin
        // wait here for something to happen
      end

      BRANCHED: begin
        valid    = 1'b0;
        do_fetch = fetch_possible;

        if (fetch_valid && (~is_crossword))
          valid = 1'b1;

        if (ready_i) begin
          if (hwloop_i) begin
            addr_n = addr_o; // keep the old address for now
            NS = HWLP_WAIT_GNT;
          end else begin
            if (next_valid) begin
              if (fetch_gnt) begin
                save_rdata_last = 1'b1;
                NS = VALID_GRANTED;
              end else
                NS = VALID;
            end else if (next_is_crossword) begin
              if (fetch_gnt) begin
                save_rdata_last = 1'b1;
                NS = NOT_VALID_CROSS_GRANTED;
              end else begin
                NS = NOT_VALID_CROSS;
              end
            end else begin
              if (fetch_gnt)
                NS = NOT_VALID_GRANTED;
              else
                NS = NOT_VALID;
            end
          end
        end else begin
          if (fetch_valid) begin
            if (is_crossword) begin
              save_rdata_last = 1'b1;
              if (fetch_gnt)
                NS = NOT_VALID_CROSS_GRANTED;
              else
                NS = NOT_VALID_CROSS;
            end else begin
              if (fetch_gnt) begin
                save_rdata_last = 1'b1;
                NS = VALID_GRANTED;
              end else
                NS = VALID;
            end
          end
        end
      end

      NOT_VALID: begin
        do_fetch = 1'b1;

        if (fetch_gnt)
          NS = NOT_VALID_GRANTED;
      end

      NOT_VALID_GRANTED: begin
        valid   = fetch_valid;
        do_hwlp = hwloop_i;

        if (fetch_valid)
          NS = VALID;
      end

      NOT_VALID_CROSS:
      begin
        do_fetch = 1'b1;

        if (fetch_gnt)
        begin
          save_rdata_last = 1'b1;
          NS = NOT_VALID_CROSS_GRANTED;
        end
      end

      NOT_VALID_CROSS_GRANTED:
      begin
        valid    = fetch_valid;
        use_last = 1'b1;
        do_hwlp  = hwloop_i;

        if (fetch_valid)
        begin
          if (ready_i)
            NS = VALID;
          else
            NS = VALID_CROSS;
        end
      end

      VALID: begin
         valid    = 1'b1;
         do_fetch = fetch_possible;  // fetch_possible  =  addr_o[3:2] == 2'b11;//
         do_hwlp  = hwloop_i;

         if (ready_i)
         begin
            if (next_is_crossword)
            begin
               do_fetch = 1'b1;

               if (fetch_gnt)
               begin
                  save_rdata_last = 1'b1;
                  NS = NOT_VALID_CROSS_GRANTED;
               end
               else // not fetching
               begin
                  NS = NOT_VALID_CROSS;
               end
            end
            else // Next is not crossword
               if (~next_valid)
               begin
                  if (fetch_gnt)
                     NS = NOT_VALID_GRANTED;
                  else
                     NS = NOT_VALID;
               end
               else // Next is valid
               begin
                  if (fetch_gnt)
                  begin
                     if (next_upper_compressed)
                     begin
                        save_rdata_last = 1'b1;
                        NS = VALID_GRANTED;
                     end
                  end
               end
         end
         else // NOT ready
         begin
            if (fetch_gnt)
               begin
                  save_rdata_last = 1'b1;
                  NS = VALID_GRANTED;
               end
         end
      end

      VALID_CROSS: begin
        valid    = 1'b1;
        use_last = 1'b1;
        do_hwlp  = hwloop_i;

        if (ready_i)
          NS = VALID;
      end

      VALID_GRANTED: begin
        valid    = 1'b1;
        use_last = 1'b1;
        do_hwlp  = hwloop_i;

        if (ready_i) begin
          if (fetch_valid) begin
            if (next_is_crossword)
              NS = VALID_CROSS;
            else if(next_upper_compressed)
              NS = VALID_FETCH_DONE;
            else
              NS = VALID;
          end else begin
            if (next_is_crossword)
              NS = NOT_VALID_CROSS_GRANTED;
            else if (next_upper_compressed)
              NS = VALID_GRANTED;
            else
              NS = NOT_VALID_GRANTED;
          end
        end else begin
          if (fetch_valid)
            NS = VALID_FETCH_DONE;
        end
      end

      VALID_FETCH_DONE: begin
        valid    = 1'b1;
        use_last = 1'b1;
        do_hwlp  = hwloop_i;

        if (ready_i) begin
          if (next_is_crossword)
            NS = VALID_CROSS;
          else if (next_upper_compressed)
            NS = VALID_FETCH_DONE;
          else
            NS = VALID;
        end
      end

      HWLP_WAIT_GNT: begin
        do_hwlp_int = 1'b1;

        if (fetch_gnt) begin
          is_hwlp_n = 1'b1;
          addr_n = hwloop_target_i;
          NS = BRANCHED;
        end
      end

      HWLP_GRANTED: begin
        valid    = 1'b1;
        use_hwlp = 1'b1;

        if (ready_i) begin
          addr_n = hwloop_target_i;

          if (fetch_valid) begin
            is_hwlp_n = 1'b1;

            if (hwlp_is_crossword) begin
              NS = NOT_VALID_CROSS;
            end else begin
              NS = VALID;
            end
          end else begin
            NS = HWLP_GRANTED_WAIT;
          end
        end else begin
          if (fetch_valid)
            NS = HWLP_FETCH_DONE;
        end
      end

      HWLP_GRANTED_WAIT: begin
        use_hwlp = 1'b1;

        if (fetch_valid) begin
          is_hwlp_n = 1'b1;

          if ( (addr_L0[3:1] == 3'b111) && (~upper_is_compressed)) begin
            NS = NOT_VALID_CROSS;
          end else begin
            NS = VALID;
          end
        end
      end

      HWLP_FETCH_DONE: begin
        valid    = 1'b1;
        use_hwlp = 1'b1;

        if (ready_i) begin
          is_hwlp_n = 1'b1;
          addr_n = hwloop_target_i;

          if (hwlp_is_crossword) begin
            NS = NOT_VALID_CROSS;
          end else begin
            NS = VALID;
          end
        end
      end
    endcase

    // branches always have priority
    if (branch_i) begin
      is_hwlp_n = 1'b0;
      addr_n    = addr_i;
      NS        = BRANCHED;

    end else if (hwloop_i) begin
      if (do_hwlp) begin
        if (ready_i) begin
          if (fetch_gnt) begin
            is_hwlp_n = 1'b1;
            addr_n = hwloop_target_i;
            NS = BRANCHED;
          end else begin
            addr_n = addr_o; // keep the old address for now
            NS = HWLP_WAIT_GNT;
          end
        end else begin
          if (fetch_gnt) begin
            save_rdata_hwlp = 1'b1;
            NS = HWLP_GRANTED;
          end
        end
      end
    end
  end


  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n)
    begin
      addr_q         <= '0;
      is_hwlp_q      <= 1'b0;
      CS             <= IDLE;
      rdata_last_q   <= '0;
    end
    else
    begin
      addr_q    <= addr_n;
      is_hwlp_q <= is_hwlp_n;

      CS <= NS;

      if (save_rdata_hwlp)
        rdata_last_q <= rdata_o;
      else if(save_rdata_last)
           begin
              //rdata_last_q <= rdata_L0[3];
              if(ready_i)
              begin
                   rdata_last_q <= rdata_L0[3];//rdata;
              end
              else
              begin
                   rdata_last_q <= rdata;//rdata;
              end
           end
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // output ports
  //////////////////////////////////////////////////////////////////////////////

  assign rdata_o = ((~addr_o[1]) || use_hwlp) ? rdata : rdata_unaligned;
  assign valid_o = valid & (~branch_i);

  assign addr_o = addr_q;

  assign is_hwlp_o = is_hwlp_q & (~branch_i);

  assign busy_o = busy_L0;


  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
  `ifndef VERILATOR
    // there should never be a ready_i without valid_o
    assert property (
      @(posedge clk) (ready_i) |-> (valid_o) ) else $warning("IF Stage is ready without prefetcher having valid data");

    // never is_crossword while also next_is_crossword
    assert property (
      @(posedge clk) (next_is_crossword) |-> (~is_crossword) ) else $warning("Cannot have two crossword accesses back-to-back");
    assert property (
      @(posedge clk) (is_crossword) |-> (~next_is_crossword) ) else $warning("Cannot have two crossword accesses back-to-back");
  `endif
endmodule // prefetch_L0_buffer

