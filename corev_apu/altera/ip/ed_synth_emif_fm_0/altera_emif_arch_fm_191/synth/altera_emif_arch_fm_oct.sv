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



module altera_emif_arch_fm_oct #(
   parameter PHY_CALIBRATED_OCT = 0
) (
   input  logic oct_rzqin, 
   output logic oct_termin 
);
   localparam OCT_USER_OCT = "A_OCT_USER_OCT_OFF";

   generate if (PHY_CALIBRATED_OCT == 1) begin
     tennm_termination term_inst (
       .req_recal (1'b0),
       .ack_recal (/*open*/),
       .rzqin     (oct_rzqin),
       .serdataout(oct_termin)
     );
   end
   endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm2RWhySuBXlG9AbE3HbTHwOJAj6ZCPGmwbYNUTcab+qWf8xi+J0WWjcXplRVhwNUN9uVKKovhRPcZFCZT0p4VJ+i7pZKiELwJm6gNtgjQYnKp27fN+/E3cPfzN++cxiL69ksN/50jhgNKTiyEWUDrgPUhyWHpocRzWJadcswBIgkDTLdfcoV5gprIoxRa7wjqc8juq1fzbDR+m63skC30xpYUENbeo1YO5W6FEh+vkiVOxEWEbS3LNxoGRAVYxzZyhnNH3tO+hgyIUBoERkTYUWIiMO2ZAibAveq0BO+aABmKflXAy4sWPAEya6W7BgtTc9zc5iHEndNqMzjdkB2U4ocnC4SHcaDorMptul7FS2h50DEnltLdli0p0Jz81ELdFLVt6J4faxiRwwIZe9o9c6ocykEqGeDESxpygDZ+UBwbwwa+lPRjesXc3SKg1Ev6udMGQfRQoRn35Hb+URaxUr0OWnWV/3wvpSJ2BRdTnBQ1PAkWbZKx82NSUg+mM+zwXNGXP0PZFEAykXbaDqKMK1xFjv5lLT0CCSWf8OwV6pSvIMBPMFGA+jIuYsYwBTNT+NR/+wbnZzVFecIcYYHoGqvwoAUemL0XvbhHH/zFo5+lSOBlbtG9AWnxPnS9mC1SM8QmAmVgBJoSEkuep9xwdgybpDJKNjYQHopTV8Zqh28fP7o5rTS7iBpE9SCaSeozSEtvq6laSHsWSIdyl05C5M4LcLPMAluCiVziuVK4ODvzm8ddEHqX4zl+TKPjzxptuCApz1L1cIWMFxnxEJEb0i"
`endif