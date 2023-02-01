// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)

module  uvmt_axi_assert (uvma_axi_intf.passive axi_assert, input bit clk, input rst_n);

   import uvm_pkg::*;


   bind uvmt_axi_assert
      uvma_axi_aw_assert         axi_aw_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvmt_axi_assert
      uvma_axi_ar_assert         axi_ar_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvmt_axi_assert
      uvma_axi_w_assert          axi_w_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvmt_axi_assert
      uvma_axi_r_assert          axi_r_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvmt_axi_assert
      uvma_axi_b_assert          axi_b_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );

   bind uvmt_axi_assert
      uvmt_cva6_axi_assert       cva6_axi_assert(.axi_assert(axi_assert),
                                            .clk(clk),
                                            .rst_n(rst_n)
                                           );


endmodule : uvmt_axi_assert
