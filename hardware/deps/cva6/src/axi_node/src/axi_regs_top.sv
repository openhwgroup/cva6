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
// Module Name:    axi_regs_top                                                  //
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
//                 @0x00 --> START ADDR REGION 0 , MASTER PORT 0                 //
//                 @0x04 --> END   ADDR REGION 0 , MASTER PORT 0                 //
//                 @0x08 --> VALID RULE REGION 0 , MASTER PORT 0                 //
//                 @0x0C --> NOT USED                                            //
//                 @0x10 --> START ADDR REGION 1 , MASTER PORT 0                 //
//                 @0x14 --> END   ADDR REGION 1 , MASTER PORT 0                 //
//                 @0x18 --> VALID RULE REGION 1 , MASTER PORT 0                 //
//                 @0x1C --> NOT USED                                            //
//                 @0x20 --> START ADDR REGION 2 , MASTER PORT 0                 //
//                 @0x24 --> END   ADDR REGION 2 , MASTER PORT 0                 //
//                 @0x28 --> VALID RULE REGION 2 , MASTER PORT 0                 //
//                 @0x2C --> NOT USED                                            //
//                 @0x30 --> START ADDR REGION 3 , MASTER PORT 0                 //
//                 @0x34 --> END   ADDR REGION 3 , MASTER PORT 0                 //
//                 @0x38 --> VALID RULE REGION 3 , MASTER PORT 0                 //
//                 @0x3C --> NOT USED                                            //
//                                                                               //
//                 @0x40 --> START ADDR REGION 0 , MASTER PORT 1                 //
//                 @0x44 --> END   ADDR REGION 0 , MASTER PORT 1                 //
//                 @0x48 --> VALID RULE REGION 0 , MASTER PORT 1                 //
//                 @0x4C --> NOT USED                                            //
//                 @0x50 --> START ADDR REGION 1 , MASTER PORT 1                 //
//                 @0x54 --> END   ADDR REGION 1 , MASTER PORT 1                 //
//                 @0x58 --> VALID RULE REGION 1 , MASTER PORT 1                 //
//                 @0x5C --> NOT USED                                            //
//                 @0x60 --> START ADDR REGION 2 , MASTER PORT 1                 //
//                 @0x64 --> END   ADDR REGION 2 , MASTER PORT 1                 //
//                 @0x68 --> VALID RULE REGION 2 , MASTER PORT 1                 //
//                 @0x6C --> NOT USED                                            //
//                 @0x70 --> START ADDR REGION 3 , MASTER PORT 1                 //
//                 @0x74 --> END   ADDR REGION 3 , MASTER PORT 1                 //
//                 @0x78 --> VALID RULE REGION 3 , MASTER PORT 1                 //
//                 @0x7C --> NOT USED                                            //
//                 .....                                                         //
//                 .....                                                         //
//                 @0x1000 --> CONNECTIVITY MAP MASTER 0                         //
//                 @0x1004 --> CONNECTIVITY MAP MASTER 1                         //
//                 @0x1008 --> CONNECTIVITY MAP MASTER 2                         //
//                 @0x100C --> CONNECTIVITY MAP MASTER 3                         //
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


module axi_regs_top
#(
    parameter C_S_AXI_ADDR_WIDTH = 32,
    parameter C_S_AXI_DATA_WIDTH = 32,

    parameter N_REGION_MAX       = 4,
    parameter N_MASTER_PORT      = 16,
    parameter N_SLAVE_PORT       = 16
)
(
    input  logic                                                                 s_axi_aclk,
    input  logic                                                                 s_axi_aresetn,
    // ADDRESS WRITE CHANNEL
    input  logic [C_S_AXI_ADDR_WIDTH-1:0]                                        s_axi_awaddr,
    input  logic                                                                 s_axi_awvalid,
    output logic                                                                 s_axi_awready,


    // ADDRESS READ CHANNEL
    input  logic [C_S_AXI_ADDR_WIDTH-1:0]                                        s_axi_araddr,
    input  logic                                                                 s_axi_arvalid,
    output logic                                                                 s_axi_arready,


    // ADDRESS WRITE CHANNEL
    input  logic [C_S_AXI_DATA_WIDTH-1:0]                                        s_axi_wdata,
    input  logic [C_S_AXI_DATA_WIDTH/8-1:0]                                      s_axi_wstrb,
    input  logic                                                                 s_axi_wvalid,
    output logic                                                                 s_axi_wready,

    input  logic                                                                 s_axi_bready,
    output logic [1:0]                                                           s_axi_bresp,
    output logic                                                                 s_axi_bvalid,

     // RESPONSE READ CHANNEL
    output logic  [C_S_AXI_DATA_WIDTH-1:0]                                       s_axi_rdata,
    output logic                                                                 s_axi_rvalid,
    input  logic                                                                 s_axi_rready,
    output logic [1:0]                                                           s_axi_rresp,

    input  logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][C_S_AXI_DATA_WIDTH-1:0]   init_START_ADDR_i,
    input  logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][C_S_AXI_DATA_WIDTH-1:0]   init_END_ADDR_i,
    input  logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0]                           init_valid_rule_i,
    input  logic [N_SLAVE_PORT-1:0][N_MASTER_PORT-1:0]                           init_connectivity_map_i,

    output logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][C_S_AXI_DATA_WIDTH-1:0]   START_ADDR_o,
    output logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0][C_S_AXI_DATA_WIDTH-1:0]   END_ADDR_o,
    output logic [N_REGION_MAX-1:0][N_MASTER_PORT-1:0]                           valid_rule_o,

    output logic [N_SLAVE_PORT-1:0][N_MASTER_PORT-1:0]                           connectivity_map_o
);

  localparam NUM_REGS           = N_MASTER_PORT*4*N_REGION_MAX + N_SLAVE_PORT;

  logic [N_SLAVE_PORT-1:0] [C_S_AXI_DATA_WIDTH-1:0]     temp_reg;

  reg                               awaddr_done_reg;
  reg                               awaddr_done_reg_dly;
  reg                               wdata_done_reg;
  reg                               wdata_done_reg_dly;
  reg                               wresp_done_reg;
  reg                               wresp_running_reg;

  reg                               araddr_done_reg;
  reg                               rresp_done_reg;
  reg                               rresp_running_reg;

  reg                               awready;
  reg                               wready;
  reg                               bvalid;

  reg                               arready;
  reg                               rvalid;

  reg      [C_S_AXI_ADDR_WIDTH-1:0] waddr_reg;
  reg      [C_S_AXI_DATA_WIDTH-1:0] wdata_reg;
  reg                         [3:0] wstrb_reg;

  reg      [C_S_AXI_ADDR_WIDTH-1:0] raddr_reg;
  reg      [C_S_AXI_DATA_WIDTH-1:0] data_out_reg;


  logic                             write_en;

  integer                           byte_index;

  integer                           k,y,w;
  genvar i,j;

  wire wdata_done_rise;
  wire awaddr_done_rise;


  logic [NUM_REGS-1:0][C_S_AXI_DATA_WIDTH/8-1:0][7:0]                   cfg_reg;                        //32bit registers
  logic [N_SLAVE_PORT-1:0][C_S_AXI_DATA_WIDTH-1:0]                      init_connectivity_map_s;        //32bit registers

  assign write_en = (wdata_done_rise & awaddr_done_reg) | (awaddr_done_rise & wdata_done_reg);
  assign wdata_done_rise = wdata_done_reg & ~wdata_done_reg_dly;
  assign awaddr_done_rise = awaddr_done_reg & ~awaddr_done_reg_dly;

  always_ff @(posedge s_axi_aclk, negedge s_axi_aresetn)
  begin
    if (!s_axi_aresetn)
    begin
      wdata_done_reg_dly  <= 0;
      awaddr_done_reg_dly <= 0;
    end
    else
    begin
      wdata_done_reg_dly  <= wdata_done_reg;
      awaddr_done_reg_dly <= awaddr_done_reg;
    end
  end

  // WRITE ADDRESS CHANNEL logic
  always_ff @(posedge s_axi_aclk, negedge s_axi_aresetn)
  begin
    if (!s_axi_aresetn)
    begin
      awaddr_done_reg <= 0;
      waddr_reg       <= 0;
      awready         <= 1;
    end
    else
    begin
      if (awready && s_axi_awvalid)
      begin
        awready   <= 0;
        awaddr_done_reg <= 1;
        waddr_reg <= {2'b00,s_axi_awaddr[31:2]};
      end
      else if (awaddr_done_reg && wresp_done_reg)
      begin
        awready   <= 1;
        awaddr_done_reg <= 0;
      end
    end
  end

  // WRITE DATA CHANNEL logic
  always_ff @(posedge s_axi_aclk, negedge s_axi_aresetn)
  begin
    if (!s_axi_aresetn)
    begin
      wdata_done_reg <= 0;
      wready         <= 1;
      wdata_reg      <= 0;
      wstrb_reg      <= 0;
    end
    else
    begin
      if (wready && s_axi_wvalid)
      begin
        wready   <= 0;
        wdata_done_reg <= 1;
        wdata_reg <= s_axi_wdata;
        wstrb_reg <= s_axi_wstrb;
      end
      else if (wdata_done_reg && wresp_done_reg)
      begin
        wready   <= 1;
        wdata_done_reg <= 0;
      end
    end
  end

  // WRITE RESPONSE CHANNEL logic
  always_ff @(posedge s_axi_aclk, negedge s_axi_aresetn)
  begin
    if (!s_axi_aresetn)
    begin
      bvalid            <= 0;
      wresp_done_reg    <= 0;
      wresp_running_reg <= 0;
    end
    else
    begin
      if (awaddr_done_reg && wdata_done_reg && !wresp_done_reg)
      begin
        if (!wresp_running_reg)
        begin
          bvalid         <= 1;
          wresp_running_reg <= 1;
        end
        else if (s_axi_bready)
        begin
          bvalid         <= 0;
          wresp_done_reg <= 1;
          wresp_running_reg <= 0;
        end
      end
      else
      begin
        bvalid         <= 0;
        wresp_done_reg <= 0;
        wresp_running_reg <= 0;
      end
    end
  end

  // READ ADDRESS CHANNEL logic
  always_ff @(posedge s_axi_aclk,  negedge s_axi_aresetn)
  begin
    if (!s_axi_aresetn)
    begin
      araddr_done_reg <= 0;
      arready         <= 1;
      raddr_reg       <= 0;
    end
    else
    begin
      if (arready && s_axi_arvalid)
      begin
        arready   <= 0;
        araddr_done_reg <= 1;
        raddr_reg <= s_axi_araddr;
      end
      else if (araddr_done_reg && rresp_done_reg)
      begin
        arready   <= 1;
        araddr_done_reg <= 0;
      end
    end
  end


  // READ RESPONSE CHANNEL logic
  always_ff @(posedge s_axi_aclk, negedge s_axi_aresetn)
  begin
    if (!s_axi_aresetn)
    begin
      rresp_done_reg    <= 0;
      rvalid            <= 0;
      rresp_running_reg <= 0;
    end
    else
    begin
      if (araddr_done_reg && !rresp_done_reg)
      begin
        if (!rresp_running_reg)
        begin
          rvalid            <= 1;
          rresp_running_reg <= 1;
        end
        else if (s_axi_rready)
        begin
          rvalid            <= 0;
          rresp_done_reg    <= 1;
          rresp_running_reg <= 0;
        end
      end
      else
      begin
        rvalid         <= 0;
        rresp_done_reg <= 0;
        rresp_running_reg <= 0;
      end
    end
  end




  generate
    if(N_MASTER_PORT < 32)
    begin
        always @(*)
        begin
          for(w = 0; w < N_SLAVE_PORT; w++)
          begin
            init_connectivity_map_s[w][N_MASTER_PORT-1:0]                  = init_connectivity_map_i[w]; //there are w arrays, each is N_MASTER_PORT bit wide
            init_connectivity_map_s[w][C_S_AXI_DATA_WIDTH-1:N_MASTER_PORT] = '0;
          end
        end
    end
    else // N_MASTER_PORT == 32
    begin
        always @(*)
        begin
          for(w = 0; w < N_SLAVE_PORT; w++)
          begin
            init_connectivity_map_s[w]                  = init_connectivity_map_i[w]; //there are w arrays, each is N_MASTER_PORT bit wide
          end
        end
    end

  endgenerate




  always_ff @( posedge s_axi_aclk, negedge s_axi_aresetn )
  begin
      if ( s_axi_aresetn == 1'b0 )
      begin


          for(y = 0; y < N_REGION_MAX; y++)
          begin
              for(k = 0; k < N_MASTER_PORT; k++)
              begin
                    cfg_reg[ (y*4) + (k*4*N_REGION_MAX) + 0]    <= init_START_ADDR_i [y][k];
                    cfg_reg[ (y*4) + (k*4*N_REGION_MAX) + 1]    <= init_END_ADDR_i   [y][k];

                    cfg_reg[ (y*4) + (k*4*N_REGION_MAX) + 2]    <= {  {(C_S_AXI_DATA_WIDTH-1) {1'b0}} , init_valid_rule_i [y][k]};

                    cfg_reg[ (y*4) + (k*4*N_REGION_MAX) + 3]    <= 32'hDEADBEEF;
              end
          end

         for(y = 0; y < N_SLAVE_PORT; y++)
         begin
                  cfg_reg[N_MASTER_PORT*4*N_REGION_MAX + y ] <= init_connectivity_map_s[y];
         end




      end
      else  if (write_en)
            begin
                  for ( byte_index = 0; byte_index <= (C_S_AXI_DATA_WIDTH/8)-1; byte_index = byte_index+1 )
                    if ( wstrb_reg[byte_index] == 1 )
                      cfg_reg[waddr_reg[7:0]][byte_index] <= wdata_reg[(byte_index*8) +: 8]; //TODO Handle Errors if we address unmapped address locations
            end

  end // SLAVE_REG_WRITE_PROC


  generate

  for(i=0;i<N_REGION_MAX;i++)
  begin
        for(j=0;j<N_MASTER_PORT;j++)
        begin
                assign START_ADDR_o [i][j]    = cfg_reg[i*4 + j*4*N_REGION_MAX + 0];
                assign END_ADDR_o   [i][j]    = cfg_reg[i*4 + j*4*N_REGION_MAX + 1];
                assign valid_rule_o [i][j]    = cfg_reg[i*4 + j*4*N_REGION_MAX + 2][0][0];
        end
  end

  for(i = 0; i < N_SLAVE_PORT; i++)
  begin
            assign temp_reg[i] = cfg_reg[N_MASTER_PORT*4*N_REGION_MAX + i];
            assign connectivity_map_o[i]  = temp_reg[i][N_MASTER_PORT-1:0];
  end

  endgenerate





  // implement slave model register read mux
  always_comb
  begin
      data_out_reg = cfg_reg[raddr_reg[7:0]];
  end // SLAVE_REG_READ_PROC

  assign s_axi_awready = awready;
  assign s_axi_wready = wready;

  assign s_axi_bresp = 2'b00;
  assign s_axi_bvalid = bvalid;

  assign s_axi_arready = arready;
  assign s_axi_rresp = 2'b00;
  assign s_axi_rvalid = rvalid;
  assign s_axi_rdata = data_out_reg;

endmodule
