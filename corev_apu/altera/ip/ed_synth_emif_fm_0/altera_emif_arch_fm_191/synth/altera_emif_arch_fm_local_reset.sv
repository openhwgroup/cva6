// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


///////////////////////////////////////////////////////////////////////////////
//  Reset request sequencing state machine.
//
///////////////////////////////////////////////////////////////////////////////
module altera_emif_arch_fm_local_reset # (
   parameter PHY_CONFIG_ENUM    = "",
   parameter IS_HPS             = 0
) (
   input  logic   afi_clk,
   input  logic   afi_reset_n,
   input  logic   emif_usr_clk,
   input  logic   emif_usr_reset_n,

   input  logic   local_reset_req_int,
   output logic   core2seq_reset_req,

   output logic   local_reset_done,
   input  logic   seq2core_reset_done
);
   timeunit 1ns;
   timeprecision 1ps;

   typedef enum {
      WAIT_RESET_DONE,
      WAIT_USER_RESET_REQ_1ST_DEASSERT,
      WAIT_USER_RESET_REQ_ASSERT,
      WAIT_USER_RESET_REQ_2ND_DEASSERT,
      ASSERT_CORE2SEQ_RESET_REQ
   } state_t;

   generate
      if (IS_HPS) begin: hps
         assign core2seq_reset_req = 1'b0;
         assign local_reset_done   = 1'b0;
      end else begin : non_hps
         logic clk;
         logic reset_n;

         if (PHY_CONFIG_ENUM == "CONFIG_PHY_AND_HARD_CTRL") begin : hmc
            assign clk = emif_usr_clk;
            assign reset_n = emif_usr_reset_n;
         end else begin : non_hmc
            assign clk = afi_clk;
            assign reset_n = afi_reset_n;
         end

         ////////////////////////////////////////////////////////////////////
         // State machine
         ////////////////////////////////////////////////////////////////////
         state_t state                 /* synthesis ignore_power_up */;
         logic   core2seq_reset_req_r  /* synthesis ignore_power_up dont_merge syn_noprune syn_preserve = 1 */;
         logic   local_reset_done_r    /* synthesis ignore_power_up dont_merge syn_noprune syn_preserve = 1 */;

         always_ff @(posedge clk, negedge reset_n)
         begin
            if (!reset_n) begin
               state                <= WAIT_RESET_DONE;
               core2seq_reset_req_r <= 1'b0;
               local_reset_done_r   <= 1'b0;
            end else begin
               case (state)
                  WAIT_RESET_DONE:
                  begin
                     // Wait until sequencer signals it's ready to accept a reset request.
                     if (seq2core_reset_done) begin
                        if (local_reset_req_int == 1'b1) begin
                           state                <= WAIT_USER_RESET_REQ_1ST_DEASSERT;
                           core2seq_reset_req_r <= 1'b0;
                           local_reset_done_r   <= 1'b1;
                        end else begin
                           state                <= WAIT_USER_RESET_REQ_ASSERT;
                           core2seq_reset_req_r <= 1'b0;
                           local_reset_done_r   <= 1'b1;
                        end
                     end
                     else
                     begin
                        state                <= WAIT_RESET_DONE;
                        core2seq_reset_req_r <= 1'b0;
                        local_reset_done_r   <= 1'b0;
                     end
                  end

                  WAIT_USER_RESET_REQ_1ST_DEASSERT:
                  begin
                     if (~local_reset_req_int) begin
                        state                <= WAIT_USER_RESET_REQ_ASSERT;
                        core2seq_reset_req_r <= 1'b0;
                        local_reset_done_r   <= 1'b1;
                     end else begin
                        state                <= WAIT_USER_RESET_REQ_1ST_DEASSERT;
                        core2seq_reset_req_r <= 1'b0;
                        local_reset_done_r   <= 1'b1;
                     end
                  end

                  WAIT_USER_RESET_REQ_ASSERT:
                  begin
                     if (local_reset_req_int) begin
                        state                <= WAIT_USER_RESET_REQ_2ND_DEASSERT;
                        core2seq_reset_req_r <= 1'b0;
                        local_reset_done_r   <= 1'b1;
                     end else begin
                        state                <= WAIT_USER_RESET_REQ_ASSERT;
                        core2seq_reset_req_r <= 1'b0;
                        local_reset_done_r   <= 1'b1;
                     end

                  end

                  WAIT_USER_RESET_REQ_2ND_DEASSERT:
                  begin
                     if (~local_reset_req_int) begin
                        state                <= ASSERT_CORE2SEQ_RESET_REQ;
                        core2seq_reset_req_r <= 1'b1;
                        local_reset_done_r   <= 1'b0;
                     end else begin
                        state                <= WAIT_USER_RESET_REQ_2ND_DEASSERT;
                        core2seq_reset_req_r <= 1'b0;
                        local_reset_done_r   <= 1'b1;
                     end
                  end

                  ASSERT_CORE2SEQ_RESET_REQ:
                  begin
                     state                   <= ASSERT_CORE2SEQ_RESET_REQ;
                     core2seq_reset_req_r    <= 1'b1;
                     local_reset_done_r      <= 1'b0;
                  end
                  default:
                  begin
                     state                   <= WAIT_RESET_DONE;
                     core2seq_reset_req_r    <= 1'b0;
                     local_reset_done_r      <= 1'b0;
                  end
               endcase
            end
         end

         ////////////////////////////////////////////////////////////////////
         // Output generation
         ////////////////////////////////////////////////////////////////////
         assign core2seq_reset_req = core2seq_reset_req_r;

         // Instead of passing seq2core_reset_done directly to user, we have the ability
         // to acknowledge the reset request earlier, as soon as a local_reset_req pulse
         // is detected.
         assign local_reset_done = local_reset_done_r;
      end
   endgenerate
endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm17Lw9A+Y1qL6DKmZb6gNVp9ibcm6scere9epDXTC/2vzfNVlWzB7JrJDsxI4z+NLDxVyeb/fRVHzbHATHTA+3LN523uM+Wv4CQEwz9JO1ReHQQBFMj9RERCsr65s4/Zk0DERrPpuIEeJVFGBx/Iqvp6YtXZNnQo8DTvrdTmC2geBEMESzW5fZ//rcOboyFXIWtfNWiy+OQwrLypjC4gUWVwvEpq/iP422FqxX09YuKbuoWpi6POlvLNJdhu5F6KT8u0vIL9+zxUCK/GUxoVl7QzvG5dYjDskh5DZ8yuSbEfnZZTvFPD3MauEbN7jnpgA8kXniSqCOpQjg83tp8Dmx0/AHba1qxSE6/ZmL8Oe0liDqw0b/zpJacWiNzXM0+ZLW+jL5iVbPRqXd7eq1E+e6s0TfSDeBFgHIwfusfMMTcsQt913WtGFxfK/e8Z2f86iM2RRSLJ3dJ6dBmrO/jj9v1B8skKwgnqZ0cncrNsd4FkHlu5/qNEXg8WjCeW3d7yHWUAreteELxypgp6N8D5qIHgdVrOU9bjt0zRGvfkMalGGC+Ic1bhQ/VekVN90ky6fSI74OJopRZBoYk7XFyjm/aB6v6Gd/iWTd0F8jjBHHPv0WgEGFCMTU2T3SUgu8Zx1AfEfxDiWqsjg3z3Bjag0vY45foDi55s22f2GjjgkrrxXmGALi4fbxAeF7vxUh+Ur8C9TjWBlU4CNO/yKX49Huugt6l728z9s18vUX8McJdSZnFPS2/fHF4CO/oKHMc8EV6RmeO7sEP36yoSAkymiIo"
`endif