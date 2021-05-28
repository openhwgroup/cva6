// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


// ============================================================================= //
// Company:        Multitherman Laboratory @ DEIS - University of Bologna        //
//                    Viale Risorgimento 2 40136                                 //
//                    Bologna - fax 0512093785 -                                 //
//                                                                               //
// Engineer:       Antonio Pullini - pullinia@iis.ee.ethz.ch                     //
//                 Igor Loi - igor.loi@unibo.it                                  //
//                                                                               //
//                                                                               //
// Additional contributions by:                                                  //
//                                                                               //
//                                                                               //
//                                                                               //
// Create Date:    01/02/2014                                                    //
// Design Name:    AXI 4 INTERCONNECT                                            //
// Module Name:    apb_regs_top                                                  //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:    This block allows for the node reconfiguration. basically is  //
//                 possible to remap each master port (memory mapped) and to     //
//                 define the connectivity map between masters and slaves.       //
//                 It is possible to define up to 4 regions for each master port.//
//                 Each Region is made of Start address, end address and Valid   //
//                 rule. Connettivity map is stored in a 32 bit register,        //
//                 therefore it is not possible to have more than 32 slave ports //
//                 The memory map is the FOLLOWING:                              //
//                                                                               //
//                 @0x000 --> START ADDR REGION 0 , MASTER PORT 0                //
//                 @0x004 --> START ADDR REGION 0 , MASTER PORT 1                //
//                 @0x008 --> START ADDR REGION 0 , MASTER PORT 2                //
//                 @0x00C --> START ADDR REGION 0 , MASTER PORT 3                //
//                 .....                                                         //
//                 @0x100 --> END ADDR REGION 0 ,   MASTER PORT 0                //
//                 @0x104 --> END ADDR REGION 0 ,   MASTER PORT 1                //
//                 @0x108 --> END ADDR REGION 0 ,   MASTER PORT 2                //
//                 @0x10C --> END ADDR REGION 0 ,   MASTER PORT 3                //
//                 .....                                                         //
//                 @0x200 --> VALID_RULE REGION 0 ,   MASTER PORT 0              //
//                 @0x204 --> VALID_RULE REGION 0 ,   MASTER PORT 1              //
//                 @0x208 --> VALID_RULE REGION 0 ,   MASTER PORT 2              //
//                 @0x20C --> VALID_RULE REGION 0 ,   MASTER PORT 3              //
//                                                                               //
//                 @0x300 --> CONNECTIVITY MAP MASTER 0                          //
//                 @0x304 --> CONNECTIVITY MAP MASTER 1                          //
//                 @0x308 --> CONNECTIVITY MAP MASTER 2                          //
//                 @0x30C --> CONNECTIVITY MAP MASTER 3                          //
//                 .....                                                         //
//                 .....                                                         //
// Revision:                                                                     //
// Revision v0.1 - 01/02/2014 : File Created                                     //
// Revision v0.2 - 30/05/2014 : Design adapted for the axi node                  //
// Revision v0.3 - 18/11/2014 : Modification in the memory map                   //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
// ============================================================================= //

module apb_regs_top
#(
    parameter APB_ADDR_WIDTH     = 12,  //APB slaves are 4KB by default
    parameter APB_DATA_WIDTH     = 32,
    parameter N_REGION_MAX       = 4,
    parameter N_MASTER_PORT      = 16,
    parameter N_SLAVE_PORT       = 16
)
(
    input  logic                                                             HCLK,
    input  logic                                                             HRESETn,
    input  logic [APB_ADDR_WIDTH-1:0]                                        PADDR_i,
    input  logic [APB_DATA_WIDTH-1:0]                                        PWDATA_i,
    input  logic                                                             PWRITE_i,
    input  logic                                                             PSEL_i,
    input  logic                                                             PENABLE_i,
    output logic [APB_DATA_WIDTH-1:0]                                        PRDATA_o,
    output logic                                                             PREADY_o,
    output logic                                                             PSLVERR_o,

    input  logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][31:0]                 init_START_ADDR_i,
    input  logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][31:0]                 init_END_ADDR_i,
    input  logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0]                       init_valid_rule_i,
    input  logic [N_SLAVE_PORT-1:0][N_MASTER_PORT-1:0]                       init_connectivity_map_i,

    output logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][31:0]                 START_ADDR_o,
    output logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][31:0]                 END_ADDR_o,
    output logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0]                       valid_rule_o,
    output logic [N_SLAVE_PORT-1:0][N_MASTER_PORT-1:0]                       connectivity_map_o
);

   logic [N_REGION_MAX*N_MASTER_PORT-1:0][31:0]                              cfg_req_START_ADDR;
   logic [N_REGION_MAX*N_MASTER_PORT-1:0][31:0]                              cfg_req_END_ADDR;
   logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0]                               cfg_req_valid_rule;
   logic [N_SLAVE_PORT-1:0][N_MASTER_PORT-1:0]                               cfg_req_connectivity_map;





   always @ (posedge HCLK /*or negedge HRESETn*/) //FIXME asynch reset
   begin
        if(~HRESETn)
        begin
            cfg_req_START_ADDR       <= init_START_ADDR_i;
            cfg_req_END_ADDR         <= init_END_ADDR_i;
            cfg_req_valid_rule       <= init_valid_rule_i;
            cfg_req_connectivity_map <= init_connectivity_map_i;
        end
        else
        begin
            if (PSEL_i && PENABLE_i && PWRITE_i)
            begin
                  case (PADDR_i[9:8])
                  2'b00: // Write Init Address
                  begin
                     cfg_req_START_ADDR[PADDR_i[7:2]]  <= PWDATA_i[31:0];
                  end

                  2'b01: // Write end address
                  begin
                      cfg_req_END_ADDR[PADDR_i[7:2]]     <= PWDATA_i[31:0];
                  end

                  2'b10: // Write Init Address
                  begin
                      cfg_req_valid_rule[PADDR_i[7:2]]  <= PWDATA_i[N_MASTER_PORT-1:0];
                  end

                  2'b11: // Write end address
                  begin
                      cfg_req_END_ADDR[PADDR_i[7:2]]    <= PWDATA_i[N_MASTER_PORT-1:0];
                  end
                  endcase
               end
          end
     end

   always_comb
   begin
            if (PSEL_i && PENABLE_i && ~PWRITE_i)
            begin
                  case (PADDR_i[9:8])
                  2'b00: // Write Init Address
                  begin
                     PRDATA_o[31:0] = cfg_req_START_ADDR[PADDR_i[7:2]];
                  end

                  2'b01: // Write end address
                  begin
                      PRDATA_o[31:0] = cfg_req_END_ADDR[PADDR_i[7:2]];
                  end

                  2'b10: // Write Init Address
                  begin
                      PRDATA_o[31:0] = cfg_req_valid_rule[PADDR_i[7:2]];
                  end

                  2'b11: // Write end address
                  begin
                      PRDATA_o[31:0] = cfg_req_END_ADDR[PADDR_i[7:2]];
                  end
                  endcase
            end
            else
              PRDATA_o = '0;
   end

   assign PREADY_o  = 1'b1;
   assign PSLVERR_o = 1'b0;

endmodule
