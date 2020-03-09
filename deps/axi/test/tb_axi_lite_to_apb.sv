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

// Description: This testbench sends random generated AXI4-Lite transfers to the bridge
//              Each APB slave is simulated by randomly updating its response signals each clock
//              Cycle. There are some assertions testing sequences for correct APB4 signaling.

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_lite_to_apb;
  // Dut parameters
  localparam int unsigned NoApbSlaves = 8;    // How many APB Slaves  there are
  localparam int unsigned NoAddrRules = 9;    // How many address rules for the APB slaves
  // Random master no Transactions
  localparam int unsigned NoWrites    = 10000;  // How many rand writes of the master
  localparam int unsigned NoReads     = 20000;  // How many rand reads of the master
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;
  // Type widths
  localparam int unsigned AxiAddrWidth = 32;
  localparam int unsigned AxiDataWidth = 32;
  localparam int unsigned AxiStrbWidth = AxiDataWidth/8;

  typedef logic [AxiAddrWidth-1:0]      addr_t;
  typedef axi_pkg::xbar_rule_32_t       rule_t; // Has to be the same width as axi addr
  typedef logic [AxiDataWidth-1:0]      data_t;
  typedef logic [AxiStrbWidth-1:0]      strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T ( aw_chan_t, addr_t         )
  `AXI_LITE_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t, strb_t )
  `AXI_LITE_TYPEDEF_B_CHAN_T  (  b_chan_t                 )

  `AXI_LITE_TYPEDEF_AR_CHAN_T ( ar_chan_t, addr_t )
  `AXI_LITE_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t )

  `AXI_LITE_TYPEDEF_REQ_T     (  axi_req_t, aw_chan_t, w_chan_t, ar_chan_t )
  `AXI_LITE_TYPEDEF_RESP_T    ( axi_resp_t,  b_chan_t,            r_chan_t )

  typedef logic [NoApbSlaves-1:0] sel_t;

  typedef struct packed {
    addr_t          paddr;
    axi_pkg::prot_t pprot;   // same as AXI, this is allowed
    logic           psel;    // onehot
    logic           penable;
    logic           pwrite;
    data_t          pwdata;
    strb_t          pstrb;
  } apb_req_t;

  typedef struct packed {
    logic  pready;
    data_t prdata;
    logic  pslverr;
  } apb_resp_t;

  localparam rule_t [NoAddrRules-1:0] AddrMap = '{
    '{idx: 32'd7, start_addr: 32'h0001_0000, end_addr: 32'h0001_1000},
    '{idx: 32'd6, start_addr: 32'h0000_9000, end_addr: 32'h0001_0000},
    '{idx: 32'd5, start_addr: 32'h0000_8000, end_addr: 32'h0000_9000},
    '{idx: 32'd4, start_addr: 32'h0002_0000, end_addr: 32'h0002_1000},
    '{idx: 32'd4, start_addr: 32'h0000_7000, end_addr: 32'h0000_8000},
    '{idx: 32'd3, start_addr: 32'h0000_6300, end_addr: 32'h0000_7000},
    '{idx: 32'd2, start_addr: 32'h0000_4000, end_addr: 32'h0000_6300},
    '{idx: 32'd1, start_addr: 32'h0000_3000, end_addr: 32'h0000_4000},
    '{idx: 32'd0, start_addr: 32'h0000_0000, end_addr: 32'h0000_3000}
  };

  typedef axi_test::rand_axi_lite_master #(
    // AXI interface parameters
    .AW       ( AxiAddrWidth  ),
    .DW       ( AxiDataWidth  ),
    // Stimuli application and test time
    .TA       ( ApplTime       ),
    .TT       ( TestTime       ),
    .MIN_ADDR ( 32'h0000_0000  ),
    .MAX_ADDR ( 32'h0002_2000  ),
    // Maximum number of open transactions
    .MAX_READ_TXNS  ( 32'd10   ),
    .MAX_WRITE_TXNS ( 32'd10   ),
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    .AX_MIN_WAIT_CYCLES (    0 ),
    .AX_MAX_WAIT_CYCLES (   10 ),
    .W_MIN_WAIT_CYCLES  (    0 ),
    .W_MAX_WAIT_CYCLES  (    5 ),
    .RESP_MIN_WAIT_CYCLES (  0 ),
    .RESP_MAX_WAIT_CYCLES ( 20 )
  ) rand_axi_lite_master_t;

  // -------------
  // DUT signals
  // -------------
  logic clk;
  // DUT signals
  logic rst_n;
  logic end_of_sim;

  // master structs
  axi_req_t  axi_req;
  axi_resp_t axi_resp;

  // slave structs
  apb_req_t  [NoApbSlaves-1:0] apb_req;
  apb_resp_t [NoApbSlaves-1:0] apb_resps;

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_LITE #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master ();
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master_dv (clk);
  `AXI_LITE_ASSIGN           ( master,  master_dv )
  `AXI_LITE_ASSIGN_TO_REQ    ( axi_req, master    )
  `AXI_LITE_ASSIGN_FROM_RESP ( master,  axi_resp  )

  // -------------------------------
  // AXI Rand Masters
  // -------------------------------
  // Master controls simulation run time
  initial begin : proc_axi_master
    static rand_axi_lite_master_t rand_axi_lite_master = new ( master_dv , "axi_lite_mst");
    end_of_sim <= 1'b0;
    rand_axi_lite_master.reset();
    @(posedge rst_n);
    rand_axi_lite_master.run(NoReads, NoWrites);
    end_of_sim <= 1'b1;
  end


  for (genvar i = 0; i < NoApbSlaves; i++) begin : gen_apb_slave
    initial begin : proc_apb_slave
      apb_resps[i] <= '0;
      forever begin
        @(posedge clk);
        apb_resps[i].pready  <= #ApplTime $urandom();
        apb_resps[i].prdata  <= #ApplTime $urandom();
        apb_resps[i].pslverr <= #ApplTime $urandom();
      end
    end
  end

  initial begin : proc_sim_stop
    @(posedge rst_n);
    wait (end_of_sim);
    $stop();
  end

  // pragma translate_off
  `ifndef VERILATOR
  // Assertions to determine correct APB protocol sequencing
  default disable iff (!rst_n);
  for (genvar i = 0; i < NoApbSlaves; i++) begin : gen_apb_assertions
    // when psel is not asserted, the bus is in the idle state
    sequence APB_IDLE;
      !apb_req[i].psel;
    endsequence

    // when psel is set and penable is not, it is the setup state
    sequence APB_SETUP;
      apb_req[i].psel && !apb_req[i].penable;
    endsequence

    // when psel and penable are set it is the access state
    sequence APB_ACCESS;
      apb_req[i].psel && apb_req[i].penable;
    endsequence

    // APB Transfer is APB state going from setup to access
    sequence APB_TRANSFER;
      APB_SETUP ##1 APB_ACCESS;
    endsequence

    apb_complete:   assert property ( @(posedge clk)
        (APB_SETUP |-> APB_TRANSFER));

    apb_penable:    assert property ( @(posedge clk)
        (apb_req[i].penable && apb_req[i].psel && apb_resps[i].pready |=> (!apb_req[i].penable)));

    control_stable: assert property ( @(posedge clk)
        (APB_TRANSFER |-> $stable({apb_req[i].pwrite, apb_req[i].paddr})));

    apb_valid:      assert property ( @(posedge clk)
        (APB_TRANSFER |-> ((!{apb_req[i].pwrite, apb_req[i].pstrb, apb_req[i].paddr}) !== 1'bx)));

    write_stable:   assert property ( @(posedge clk)
        ((apb_req[i].penable && apb_req[i].pwrite) |-> $stable(apb_req[i].pwdata)));

    strb_stable:    assert property ( @(posedge clk)
        ((apb_req[i].penable && apb_req[i].pwrite) |-> $stable(apb_req[i].pstrb)));
  end
  `endif
  // pragma translate_on

  //-----------------------------------
  // Clock generator
  //-----------------------------------
    clk_rst_gen #(
    .CLK_PERIOD    ( CyclTime ),
    .RST_CLK_CYCLES( 5        )
  ) i_clk_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_lite_to_apb #(
    .NoApbSlaves    ( NoApbSlaves  ),
    .NoRules        ( NoAddrRules  ),
    .AddrWidth      ( AxiAddrWidth ),
    .DataWidth      ( AxiDataWidth ),
    .axi_lite_req_t ( axi_req_t    ),
    .axi_lite_resp_t( axi_resp_t   ),
    .apb_req_t      ( apb_req_t    ),
    .apb_resp_t     ( apb_resp_t   ),
    .rule_t         ( rule_t       )
  ) i_axi_lite_to_apb_dut (
    .clk_i           ( clk          ),
    .rst_ni          ( rst_n        ),
    .axi_lite_req_i  ( axi_req      ),
    .axi_lite_resp_o ( axi_resp     ),
    .apb_req_o       ( apb_req      ),
    .apb_resp_i      ( apb_resps    ),
    .addr_map_i      ( AddrMap      )
  );
endmodule
