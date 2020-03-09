// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// Directed Random Verification Testbench for `axi_lite_xbar`:  The crossbar is instantiated with
// a number of random axi master and slave modules. Each random master executes a fixed number of
// writes and reads over the whole addess map. All masters simultaneously issue transactions
// through the crossbar, thereby fully saturating all its bandwidth.

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_lite_xbar;
  // Dut parameters
  localparam int unsigned NoMasters   = 32'd6;    // How many Axi Masters there are
  localparam int unsigned NoSlaves    = 32'd8;    // How many Axi Slaves  there are
  // Random master no Transactions
  localparam int unsigned NoWrites   = 32'd10000;  // How many writes per master
  localparam int unsigned NoReads    = 32'd10000;  // How many reads per master
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;
  // axi configuration
  localparam int unsigned AxiAddrWidth      =  32'd32;    // Axi Address Width
  localparam int unsigned AxiDataWidth      =  32'd64;    // Axi Data Width
  localparam int unsigned AxiStrbWidth      =  AxiDataWidth / 32'd8;
  // in the bench can change this variables which are set here freely
  localparam axi_pkg::xbar_cfg_t xbar_cfg = '{
    NoSlvPorts:         NoMasters,
    NoMstPorts:         NoSlaves,
    MaxMstTrans:        32'd10,
    MaxSlvTrans:        32'd6,
    FallThrough:        1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_AX,
    AxiAddrWidth:       AxiAddrWidth,
    AxiDataWidth:       AxiDataWidth,
    NoAddrRules:        32'd8,
    default:            '0
  };
  typedef logic [AxiAddrWidth-1:0]      addr_t;
  typedef axi_pkg::xbar_rule_32_t       rule_t; // Has to be the same width as axi addr
  typedef logic [AxiDataWidth-1:0]      data_t;
  typedef logic [AxiStrbWidth-1:0]      strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T ( aw_chan_lite_t, addr_t         )
  `AXI_LITE_TYPEDEF_W_CHAN_T  (  w_chan_lite_t, data_t, strb_t )
  `AXI_LITE_TYPEDEF_B_CHAN_T  (  b_chan_lite_t                 )

  `AXI_LITE_TYPEDEF_AR_CHAN_T ( ar_chan_lite_t, addr_t )
  `AXI_LITE_TYPEDEF_R_CHAN_T  (  r_chan_lite_t, data_t )

  `AXI_LITE_TYPEDEF_REQ_T  (  req_lite_t, aw_chan_lite_t, w_chan_lite_t, ar_chan_lite_t )
  `AXI_LITE_TYPEDEF_RESP_T ( resp_lite_t,  b_chan_lite_t, r_chan_lite_t                 )

  localparam rule_t [xbar_cfg.NoAddrRules-1:0] AddrMap = '{
    '{idx: 32'd7, start_addr: 32'h0001_0000, end_addr: 32'h0001_1000},
    '{idx: 32'd6, start_addr: 32'h0000_9000, end_addr: 32'h0001_0000},
    '{idx: 32'd5, start_addr: 32'h0000_8000, end_addr: 32'h0000_9000},
    '{idx: 32'd4, start_addr: 32'h0000_7000, end_addr: 32'h0000_8000},
    '{idx: 32'd3, start_addr: 32'h0000_6300, end_addr: 32'h0000_7000},
    '{idx: 32'd2, start_addr: 32'h0000_4000, end_addr: 32'h0000_6300},
    '{idx: 32'd1, start_addr: 32'h0000_3000, end_addr: 32'h0000_4000},
    '{idx: 32'd0, start_addr: 32'h0000_0000, end_addr: 32'h0000_3000}
  };

  typedef axi_test::rand_axi_lite_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth       ),
    .DW ( AxiDataWidth       ),
    // Stimuli application and test time
    .TA ( ApplTime           ),
    .TT ( TestTime           ),
    .MIN_ADDR ( 32'h0000_0000 ),
    .MAX_ADDR ( 32'h0001_3000 ),
    .MAX_READ_TXNS  ( 10 ),
    .MAX_WRITE_TXNS ( 10 )
  ) rand_lite_master_t;
  typedef axi_test::rand_axi_lite_slave #(
    // AXI interface parameters
    .AW ( AxiAddrWidth       ),
    .DW ( AxiDataWidth       ),
    // Stimuli application and test time
    .TA ( ApplTime           ),
    .TT ( TestTime           )
  ) rand_lite_slave_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic [NoMasters-1:0] end_of_sim;

  // master structs
  req_lite_t  [NoMasters-1:0] masters_req;
  resp_lite_t [NoMasters-1:0] masters_resp;

  // slave structs
  req_lite_t  [NoSlaves-1:0] slaves_req;
  resp_lite_t [NoSlaves-1:0] slaves_resp;

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_LITE #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master [NoMasters-1:0] ();
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master_dv [NoMasters-1:0] (clk);
  for (genvar i = 0; i < NoMasters; i++) begin : gen_conn_dv_masters
    `AXI_LITE_ASSIGN           ( master[i],      master_dv[i]    )
    `AXI_LITE_ASSIGN_TO_REQ    ( masters_req[i], master[i]       )
    `AXI_LITE_ASSIGN_FROM_RESP ( master[i],      masters_resp[i] )
  end

  AXI_LITE #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     )
  ) slave [NoSlaves-1:0] ();
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     )
  ) slave_dv [NoSlaves-1:0](clk);
  for (genvar i = 0; i < NoSlaves; i++) begin : gen_conn_dv_slaves
    `AXI_LITE_ASSIGN          ( slave_dv[i],    slave[i]      )
    `AXI_LITE_ASSIGN_FROM_REQ ( slave[i],       slaves_req[i] )
    `AXI_LITE_ASSIGN_TO_RESP  ( slaves_resp[i], slave[i]      )
  end
  // -------------------------------
  // AXI Rand Masters and Slaves
  // -------------------------------
  // Masters control simulation run time
  for (genvar i = 0; i < NoMasters; i++) begin : gen_rand_master
    initial begin : proc_generate_traffic
      automatic rand_lite_master_t lite_axi_master = new ( master_dv[i], $sformatf("MST_%0d", i));
      automatic data_t          data = '0;
      automatic axi_pkg::resp_t resp = '0;
      end_of_sim[i] <= 1'b0;
      lite_axi_master.reset();
      @(posedge rst_n);
      lite_axi_master.write(32'h0000_1100, 64'hDEADBEEFDEADBEEF, 8'hFF, resp);
      lite_axi_master.read(32'h0000_e100, data, resp);
      lite_axi_master.run(NoReads, NoWrites);
      end_of_sim[i] <= 1'b1;
    end
  end

  for (genvar i = 0; i < NoSlaves; i++) begin : gen_rand_slave
    initial begin : proc_recieve_traffic
      automatic rand_lite_slave_t lite_axi_slave = new( slave_dv[i] , $sformatf("SLV_%0d", i));
      lite_axi_slave.reset();
      @(posedge rst_n);
      lite_axi_slave.run();
    end
  end

  initial begin : proc_stop_sim
    wait (&end_of_sim);
    repeat (1000) @(posedge clk);
    $display("Simulation stopped as all Masters transferred their data, Success.",);
    $stop();
  end

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .CLK_PERIOD    ( CyclTime ),
    .RST_CLK_CYCLES( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_lite_xbar #(
    .Cfg       ( xbar_cfg       ),
    .aw_chan_t ( aw_chan_lite_t ),
    .w_chan_t  (  w_chan_lite_t ),
    .b_chan_t  (  b_chan_lite_t ),
    .ar_chan_t ( ar_chan_lite_t ),
    .r_chan_t  (  r_chan_lite_t ),
    .req_t     (  req_lite_t    ),
    .resp_t    ( resp_lite_t    ),
    .rule_t    ( rule_t         )
  ) i_xbar_dut (
    .clk_i      ( clk      ),
    .rst_ni     ( rst_n    ),
    .test_i     ( 1'b0     ),
    .slv_ports_req_i  ( masters_req  ),
    .slv_ports_resp_o ( masters_resp ),
    .mst_ports_req_o  ( slaves_req   ),
    .mst_ports_resp_i ( slaves_resp  ),
    .addr_map_i       ( AddrMap      ),
    .en_default_mst_port_i ( '0      ),
    .default_mst_port_i    ( '0      )
  );
endmodule
