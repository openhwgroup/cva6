// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

/// Simulation-Only dumper for AXI transactions
///
/// This module writes all handshaked AXI beats to a log file. To use in simulation,
/// ensure `TARGET_SIMULATION` is defined.
module axi_dumper #(
  parameter      BusName   = "axi_bus",
  parameter bit  LogAW     = 1'b1,
  parameter bit  LogAR     = 1'b1,
  parameter bit  LogW      = 1'b0,
  parameter bit  LogB      = 1'b0,
  parameter bit  LogR      = 1'b0,
  parameter type axi_req_t  = logic,
  parameter type axi_resp_t = logic
) (
  input logic clk_i,
  input logic rst_ni,
  input axi_req_t axi_req_i,
  input axi_resp_t axi_resp_i
);

`ifdef TARGET_SIMULATION
  string fn;
  integer f;
  initial begin
    #1;
    $sformat(fn, "axi_trace_%s.log", BusName);
    f = $fopen(fn, "w");
    $display("[Tracer] Logging axi accesses to %s", fn);
  end

  always_ff @(posedge clk_i) begin : proc_tracer
    automatic string aw_data [string];
    automatic string ar_data [string];
    automatic string  w_data [string];
    automatic string  b_data [string];
    automatic string  r_data [string];

    automatic string aw_string;
    automatic string ar_string;
    automatic string  w_string;
    automatic string  b_string;
    automatic string  r_string;

    if (rst_ni) begin
      aw_data = '{
        "type"   : "\"AW\"",
        "time"   : $sformatf("%d", $time()),
        "id"     : $sformatf("0x%0x", axi_req_i.aw.id),
        "addr"   : $sformatf("0x%0x", axi_req_i.aw.addr),
        "len"    : $sformatf("0x%0x", axi_req_i.aw.len),
        "size"   : $sformatf("0x%0x", axi_req_i.aw.size),
        "burst"  : $sformatf("0x%0x", axi_req_i.aw.burst),
        "lock"   : $sformatf("0x%0x", axi_req_i.aw.lock),
        "cache"  : $sformatf("0x%0x", axi_req_i.aw.cache),
        "prot"   : $sformatf("0x%0x", axi_req_i.aw.prot),
        "qos"    : $sformatf("0x%0x", axi_req_i.aw.qos),
        "region" : $sformatf("0x%0x", axi_req_i.aw.region),
        "atop"   : $sformatf("0x%0x", axi_req_i.aw.atop),
        "user"   : $sformatf("0x%0x", axi_req_i.aw.user)
      };
      ar_data = '{
        "type"   : "\"AR\"",
        "time"   : $sformatf("%d", $time()),
        "id"     : $sformatf("0x%0x", axi_req_i.ar.id),
        "addr"   : $sformatf("0x%0x", axi_req_i.ar.addr),
        "len"    : $sformatf("0x%0x", axi_req_i.ar.len),
        "size"   : $sformatf("0x%0x", axi_req_i.ar.size),
        "burst"  : $sformatf("0x%0x", axi_req_i.ar.burst),
        "lock"   : $sformatf("0x%0x", axi_req_i.ar.lock),
        "cache"  : $sformatf("0x%0x", axi_req_i.ar.cache),
        "prot"   : $sformatf("0x%0x", axi_req_i.ar.prot),
        "qos"    : $sformatf("0x%0x", axi_req_i.ar.qos),
        "region" : $sformatf("0x%0x", axi_req_i.ar.region),
        "user"   : $sformatf("0x%0x", axi_req_i.ar.user)
      };
      w_data = '{
        "type" : "\"W\"",
        "time" : $sformatf("%d", $time()),
        "data" : $sformatf("0x%0x", axi_req_i.w.data),
        "strb" : $sformatf("0x%0x", axi_req_i.w.strb),
        "last" : $sformatf("0x%0x", axi_req_i.w.last),
        "user" : $sformatf("0x%0x", axi_req_i.w.user)
      };
      b_data = '{
        "type" : "\"B\"",
        "time" : $sformatf("%d", $time()),
        "id"   : $sformatf("0x%0x", axi_resp_i.b.id),
        "resp" : $sformatf("0x%0x", axi_resp_i.b.resp),
        "user" : $sformatf("0x%0x", axi_resp_i.b.user)
      };
      r_data = '{
        "type" : "\"R\"",
        "time" : $sformatf("%d", $time()),
        "id"   : $sformatf("0x%0x", axi_resp_i.r.id),
        "data" : $sformatf("0x%0x", axi_resp_i.r.data),
        "resp" : $sformatf("0x%0x", axi_resp_i.r.resp),
        "last" : $sformatf("0x%0x", axi_resp_i.r.last),
        "user" : $sformatf("0x%0x", axi_resp_i.r.user)
      };
      if (LogAW && axi_req_i.aw_valid && axi_resp_i.aw_ready) begin
        aw_string = "{";
        foreach(aw_data[key]) aw_string = $sformatf("%s'%s': %s, ", aw_string, key, aw_data[key]);
        aw_string = $sformatf("%s}", aw_string);
        $fwrite(f, aw_string);
        $fwrite(f, "\n");
      end
      if (LogAR && axi_req_i.ar_valid && axi_resp_i.ar_ready) begin
        ar_string = "{";
        foreach(ar_data[key]) ar_string = $sformatf("%s'%s': %s, ", ar_string, key, ar_data[key]);
        ar_string = $sformatf("%s}", ar_string);
        $fwrite(f, ar_string);
        $fwrite(f, "\n");
      end
      if (LogW && axi_req_i.w_valid && axi_resp_i.w_ready) begin
        w_string = "{";
        foreach(w_data[key]) w_string = $sformatf("%s'%s': %s, ", w_string, key, w_data[key]);
        w_string = $sformatf("%s}", w_string);
        $fwrite(f, w_string);
        $fwrite(f, "\n");
      end
      if (LogB && axi_resp_i.b_valid && axi_req_i.b_ready) begin
        b_string = "{";
        foreach(b_data[key]) b_string = $sformatf("%s'%s': %s, ", b_string, key, b_data[key]);
        b_string = $sformatf("%s}", b_string);
        $fwrite(f, b_string);
        $fwrite(f, "\n");
      end
      if (LogR && axi_resp_i.r_valid && axi_req_i.r_ready) begin
        r_string = "{";
        foreach(r_data[key]) r_string = $sformatf("%s'%s': %s, ", r_string, key, r_data[key]);
        r_string = $sformatf("%s}", r_string);
        $fwrite(f, r_string);
        $fwrite(f, "\n");
      end
    end
  end
  final begin
    $fclose(f);
  end

`endif

endmodule


`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_dumper_intf #(
  parameter              BusName        = "axi_bus",
  parameter bit          LogAW          = 1'b1,
  parameter bit          LogAR          = 1'b1,
  parameter bit          LogW           = 1'b0,
  parameter bit          LogB           = 1'b0,
  parameter bit          LogR           = 1'b0,
  parameter int unsigned AXI_ID_WIDTH   = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0
) (
  input logic clk_i,
  input logic rst_ni,
  AXI_BUS_DV.Monitor axi_bus
);

  typedef logic [AXI_ID_WIDTH-1:0]       id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t                     axi_req;
  axi_resp_t                    axi_resp;

  `AXI_ASSIGN_TO_REQ(axi_req, axi_bus)
  `AXI_ASSIGN_TO_RESP(axi_resp, axi_bus)

  axi_dumper #(
    .BusName    ( BusName    ),
    .LogAW      ( LogAW      ),
    .LogAR      ( LogAR      ),
    .LogW       ( LogW       ),
    .LogB       ( LogB       ),
    .LogR       ( LogR       ),
    .axi_req_t  ( axi_req_t  ),
    .axi_resp_t ( axi_resp_t )
  ) i_axi_dumper (
    .clk_i,
    .rst_ni,
    .axi_req_i  ( axi_req  ),
    .axi_resp_i ( axi_resp )
  );

endmodule
