// Copyright 2021 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module apb_fll_if_wrap #(
    parameter APB_ADDR_WIDTH = 32
) (
    input  logic                       clk_i,
    input  logic                       rst_ni,
    APB_BUS.Slave                      apb_fll_slave,
    FLL_BUS.Master                     soc_fll_master,
    FLL_BUS.Master                     per_fll_master,
    FLL_BUS.Master                     cluster_fll_master
   );
   
  

   apb_fll_if #(.APB_ADDR_WIDTH(APB_ADDR_WIDTH)) apb_fll_if_i (
        .HCLK        ( clk_i                   ),
        .HRESETn     ( rst_ni                  ),

        .PADDR       ( apb_fll_slave.paddr     ),
        .PWDATA      ( apb_fll_slave.pwdata    ),
        .PWRITE      ( apb_fll_slave.pwrite    ),
        .PSEL        ( apb_fll_slave.psel      ),
        .PENABLE     ( apb_fll_slave.penable   ),
        .PRDATA      ( apb_fll_slave.prdata    ),
        .PREADY      ( apb_fll_slave.pready    ),
        .PSLVERR     ( apb_fll_slave.pslverr   ),

        .fll1_req_o    ( soc_fll_master.req      ),
        .fll1_wrn_o    ( soc_fll_master.wrn      ),
        .fll1_add_o    ( soc_fll_master.add[1:0] ),
        .fll1_data_o   ( soc_fll_master.data     ),
        .fll1_ack_i    ( soc_fll_master.ack      ),
        .fll1_r_data_i ( soc_fll_master.r_data   ),
        .fll1_lock_i   ( soc_fll_master.lock     ),

        .fll2_req_o    ( per_fll_master.req      ),
        .fll2_wrn_o    ( per_fll_master.wrn      ),
        .fll2_add_o    ( per_fll_master.add[1:0] ),
        .fll2_data_o   ( per_fll_master.data     ),
        .fll2_ack_i    ( per_fll_master.ack      ),
        .fll2_r_data_i ( per_fll_master.r_data   ),
        .fll2_lock_i   ( per_fll_master.lock     ),

        .fll3_req_o    ( cluster_fll_master.req      ),
        .fll3_wrn_o    ( cluster_fll_master.wrn      ),
        .fll3_add_o    ( cluster_fll_master.add[1:0] ),
        .fll3_data_o   ( cluster_fll_master.data     ),
        .fll3_ack_i    ( cluster_fll_master.ack      ),
        .fll3_r_data_i ( cluster_fll_master.r_data   ),
        .fll3_lock_i   ( cluster_fll_master.lock     )
    );   

endmodule
