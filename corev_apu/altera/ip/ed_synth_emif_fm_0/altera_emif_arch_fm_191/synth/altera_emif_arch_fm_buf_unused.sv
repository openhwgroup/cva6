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


module altera_emif_arch_fm_buf_unused (
   output logic o
);
   timeunit 1ns;
   timeprecision 1ps;

   assign o = 1'b0;
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm21Y3h4ZwmeCDLBi13DER8P/hE/05XIB+MP/tekkMHRc9fTpd07EtcbE+kKx+HhUC4VAUpq+6rJcdeYx9KymU9PVChpn2OMmtAq2PDxwE2Pvtf74Ig29FfLOCq2BK/7k7HjfqtVr/sqRiw8Jc6131zcHfbOam2soohRXzrz1NAn1zeypc7b7sPbSAvEk7ndfpjwLMeZSspCCFzSoSyQ6dvzYtlDVmeteHOTh3ATroJrmeUBFxGPDC4IXy9KLm5A4yB6uUEOJGrPudw4+X7AIJo92wAbvg8mNUEnR6E0UyBBQ4MSphh3wViQ3rdc1N3QZWufydLLwkiGprss+uAfxBrvUAv6DF+N/JyY1VVQ+4dN4Txi+O2SIDk1Ts9qPlMnsRpS5Y3LPbPd3V/oKm73IQwdObN2otvOzAc73VDTZmrJZO8bqL0E0IikLpCuP7TjjALgBOPWKxXNtL0GzyNtwjoObtBzoaB1SizhMC5vq1uqYX9qYDoJrHeGK12KwKNGPLpCWgi0quSmkfqJMWPhzdCTy8eXAWsYCc1mRLycDX3gekhOqjQkJtz92W/5FGw/wkxWpXmKL5u1ufs0H87Yb61u1RrO/whVOSRqhdMJJrwkGgVTcsnq2Po/NNJ1NaNKyWlEqZzxQgG+zk14hgBdxa+sdDOSp+o+lz2y1FdSWJJVQ1DCp8UwyypZd2boAAIoj9/nogzfp3Rq/mEg7CUdOfzwbkbb9SrYIG28ncvJWvoxDgoHiqmszxVN2hgV+0IMD8NfcteSZrbk1L+SKRfGGpgk"
`endif