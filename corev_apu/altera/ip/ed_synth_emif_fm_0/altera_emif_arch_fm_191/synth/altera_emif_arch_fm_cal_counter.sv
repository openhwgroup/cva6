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



module altera_emif_arch_fm_cal_counter # (
   parameter IS_HPS = 0
) (
   input logic pll_ref_clk_int,
   input logic local_reset_req_int,
   input logic afi_cal_in_progress
);
   timeunit 1ps;
   timeprecision 1ps;

   typedef enum {
      INIT,
      IDLE,
      COUNT_CAL,
      STOP
   } counter_state_t;

   logic                         done;
   logic [31:0]                  clk_counter;

   generate
      if (IS_HPS == 0) begin : non_hps
         logic                         cal_done;
         logic                         reset_req_sync;
         logic                         cal_in_progress_sync;

         altera_std_synchronizer_nocut
         inst_sync_reset_n (
            .clk     (pll_ref_clk_int),
            .reset_n (1'b1),
            .din     (local_reset_req_int),
            .dout    (reset_req_sync)
         );

         altera_std_synchronizer_nocut
         inst_sync_cal_in_progress (
            .clk     (pll_ref_clk_int),
            .reset_n (1'b1),
            .din     (afi_cal_in_progress),
            .dout    (cal_in_progress_sync)
         );

         counter_state_t counter_state /* synthesis ignore_power_up */;

         assign done = ((counter_state == STOP) ? 1'b1 : 1'b0);

         always_ff @(posedge pll_ref_clk_int) begin
            if(reset_req_sync == 1'b1) begin
               counter_state <= INIT;
            end
            else begin
               case(counter_state)
                  INIT:
                  begin
                     clk_counter <= 32'h0;
                     counter_state <= IDLE;
                  end

                  IDLE:
                  begin
                     if (cal_in_progress_sync == 1'b1)
                     begin
                        counter_state <= COUNT_CAL;
                     end
                  end

                  COUNT_CAL:
                  begin
                     clk_counter[31:0] <= clk_counter[31:0] + 32'h0000_0001;

                     if (cal_in_progress_sync == 1'b0)
                     begin
                        counter_state <= STOP;
                     end
                  end

                  STOP:
                  begin
                     counter_state <= STOP;
                  end

                  default:
                  begin
                     counter_state <= INIT;
                  end
               endcase
            end
         end
      end else begin : hps
         assign done = 1'b1;
         assign clk_counter = '0;
      end
   endgenerate

`ifdef ALTERA_EMIF_ENABLE_ISSP
   altsource_probe #(         
      .sld_auto_instance_index ("YES"),
      .sld_instance_index      (0),
      .instance_id             ("CALC"),
      .probe_width             (33),
      .source_width            (0),
      .source_initial_value    ("0"),
      .enable_metastability    ("NO")
      ) cal_counter_issp (
      .probe  ({done, clk_counter[31:0]})
   );
`endif

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm3ajnRlCoTycdS5rLOAtZ6M6huxrgTizglD8CjFQHox2DR3mB7yrrtaKHIjqDW2jh+v84NRIUDYBdKhTW51/7O2DZsh64KUeoDc53EsrQLtn2yLnMIoCa9vcO9HjOLLTJBkJZAwMWlCwM6ei3SJGHwjp1fMp8oGysL/awCnW1Mpi+mWbH4Mr/HvaRj5xN29UVZCCwSlV4hyIdsy3K7ag/iO6ljXQEHSyRPjq0ofMN2NFNLDRFKZT4eE+3k+5pKTbSmSRZGgpAUnbw6sWJ2Fa3NpXHdRnvr4uq9ylg4Pz0RJ5+C7yu4kJBrQm2Vt8h5rmMVGp9cGn9Ub17Odi9OZLJfyAB5u+SkBp6JPOSO/KZrARP1hkWsUPqGyu7WX0YGkVGDOX34vNFFyd5E0wZCI9gkCLYieq7t5SzhXbvIKKALvlMcOxpWDPv48I7Q50qRl7LbKmM5C+Bopp4TT/UDW/3woKHg3EK9QbeqUBaAzlqPHo6r8Fbd3cgLXBuYytFja6jlPohYMJUNR1xilbJZOCE1Mj+IqYKX5UpSAZtKSsgDvsTYihdrKVj74NEExrgYleQ4t+Q2zOb7YSGRC3CML0xFA9H6wuCB+R6s1uAt83gYKVBIDcRJ6ZeAtygjgh9DDa9XrYejBayHUmqn6IB0dpltElm/nD+x7XRI6JFKetcLKOgMTxykFiWFDCLY20NopPEdPKj8cL+kGrEQAGk8JvHDraqlwCerSMeTnmOy595DvdgK3hJS221B/oP9xAPlBTBfsl9pQsmaPhhdzUD1t4FYI"
`endif