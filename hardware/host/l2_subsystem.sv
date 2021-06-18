// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Luca Valente, University of Bologna
// Date: 18.06.2020
// Description: L2 subsystem

module l2_subsystem 
#(
  parameter int unsigned NB_L2_BANKS        = 4,
  parameter int unsigned L2_BANK_SIZE       = 32768 , // 2^15 words (32 bits)
  parameter int unsigned L2_BANK_ADDR_WIDTH = $clog2(L2_BANK_SIZE),
  parameter int unsigned L2_DATA_WIDTH      = 32 , // Do not change
  localparam AXI64_2_TCDM32_N_PORTS         = 4 // Do not change, to achieve full bandwith from 64 bit AXI and 32 bit tcdm we need 4 ports!    
                                               // It is hardcoded in the axi2tcdm_wrap module.
) 
(
  input  logic          clk_i,
  input  logic          rst_ni,
  XBAR_TCDM_BUS.Slave   axi_bridge_2_interconnect[AXI64_2_TCDM32_N_PORTS-1:0]
);
   



   logic [AXI64_2_TCDM32_N_PORTS-1:0]                          core_req_l2;
   logic [AXI64_2_TCDM32_N_PORTS-1:0] [31:0]                   core_add_l2;
   logic [AXI64_2_TCDM32_N_PORTS-1:0]                          core_wen_l2;
   logic [AXI64_2_TCDM32_N_PORTS-1:0] [L2_DATA_WIDTH-1:0]      core_wdata_l2;
   logic [AXI64_2_TCDM32_N_PORTS-1:0] [3:0]                    core_be_l2;
   logic [AXI64_2_TCDM32_N_PORTS-1:0]                          core_gnt_l2;
   logic [AXI64_2_TCDM32_N_PORTS-1:0]                          core_r_valid_l2;
   logic [AXI64_2_TCDM32_N_PORTS-1:0] [L2_DATA_WIDTH-1:0]      core_r_rdata_l2;
 
   // binding
   generate
    for(genvar i=0; i<AXI64_2_TCDM32_N_PORTS; i++) begin : axi_bridge_2_interconnect_unrolling
      assign core_req_l2    [i] = axi_bridge_2_interconnect[i].req;
      assign core_add_l2    [i] = axi_bridge_2_interconnect[i].add  - ariane_soc::L2SPMBase;
      assign core_wen_l2    [i] = axi_bridge_2_interconnect[i].wen;
      assign core_be_l2     [i] = axi_bridge_2_interconnect[i].be;
      assign core_wdata_l2  [i] = axi_bridge_2_interconnect[i].wdata;
      assign axi_bridge_2_interconnect[i].gnt     = core_gnt_l2     [i];

       
      assign axi_bridge_2_interconnect[i].r_rdata = core_r_rdata_l2 [i];
      assign axi_bridge_2_interconnect[i].r_valid = core_r_valid_l2 [i];
      assign axi_bridge_2_interconnect[i].r_opc   = '0;
    end // cores_unrolling
   endgenerate
     
  logic [NB_L2_BANKS-1:0]                          mem_req_l2;
  logic [NB_L2_BANKS-1:0]                          mem_wen_l2;
  logic [NB_L2_BANKS-1:0]                          mem_gnt_l2;
  logic [NB_L2_BANKS-1:0][L2_BANK_ADDR_WIDTH-1:0]  mem_addr_l2;
  logic [NB_L2_BANKS-1:0][3:0]                     mem_be_l2;
  logic [NB_L2_BANKS-1:0][L2_DATA_WIDTH-1:0]       mem_wdata_l2;
  logic [NB_L2_BANKS-1:0][L2_DATA_WIDTH-1:0]       mem_rdata_l2;

  tcdm_interconnect #(
    .NumIn        ( AXI64_2_TCDM32_N_PORTS      ),
    .NumOut       ( NB_L2_BANKS                 ), // NUM BANKS
    .AddrWidth    ( 32                          ),
    .DataWidth    ( L2_DATA_WIDTH               ),
    .AddrMemWidth ( L2_BANK_ADDR_WIDTH          ),
    .WriteRespOn  ( 1                           ),
    .RespLat      ( 1                           ),
    .Topology     ( tcdm_interconnect_pkg::LIC  )
  ) i_tcdm_interconnect (
    .clk_i,
    .rst_ni,
    .req_i    ( core_req_l2                            ),
    .add_i    ( core_add_l2                            ),
    .wen_i    ( core_wen_l2                            ),
    .wdata_i  ( core_wdata_l2                          ),
    .be_i     ( core_be_l2                             ),
    .gnt_o    ( core_gnt_l2                            ),                        
    .vld_o    ( core_r_valid_l2                        ),
    .rdata_o  ( core_r_rdata_l2                        ),
                         
    .req_o    ( mem_req_l2                         ),
    .gnt_i    ( mem_gnt_l2                         ),
    .add_o    ( mem_addr_l2                        ),
    .wen_o    ( mem_wen_l2                         ),
    .wdata_o  ( mem_wdata_l2                       ),
    .be_o     ( mem_be_l2                          ),
    .rdata_i  ( mem_rdata_l2                       )
  );



       for(genvar i=0; i<NB_L2_BANKS; i++) begin : CUTS

        //Perform TCDM handshaking for constant 1 cycle latency
        assign mem_gnt_l2[i] = mem_req_l2[i];
          
          tc_sram #(
            .NumWords  ( L2_BANK_SIZE        ), // 2^15 lines of 32 bits each (128kB), 4 Banks -> 512 kB total memory
            .DataWidth ( L2_DATA_WIDTH       ),
            .NumPorts  ( 1                   ),
            .SimInit   ( "none"              )
          ) bank_i (
            .clk_i,
            .rst_ni,
            .req_i   (  mem_req_l2[i]                                    ),
            .we_i    (  ~mem_wen_l2[i]                                   ),
            .addr_i  (  mem_addr_l2[i]                                   ),
            .wdata_i (  mem_wdata_l2[i]                                  ),
            .be_i    (  mem_be_l2[i]                                     ),
            .rdata_o (  mem_rdata_l2[i]                                  )
          );


       end // block: CUTS
      
endmodule
