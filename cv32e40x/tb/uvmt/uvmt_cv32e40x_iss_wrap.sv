//
// Copyright 2020 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//

`ifndef __UVMT_CV32E40X_ISS_WRAP_SV__
`define __UVMT_CV32E40X_ISS_WRAP_SV__

/**
 * Module wrapper for Imperas OVP.
 * Instanitates "CPU", the OVP wrapper, and "RAM" a spare memory model.
 */
module uvmt_cv32e40x_iss_wrap
  import uvm_pkg::*;
  #(
    parameter int ROM_START_ADDR = 'h00000000,
    parameter int ROM_BYTE_SIZE  = 'h0,
    parameter int RAM_BYTE_SIZE  = 'h1B000000,
    parameter int ID = 0
   )

   (
    input realtime                clk_period,
    uvma_clknrst_if               clknrst_if
   );

   RVVI_bus     bus();
   RVVI_io      io();

   MONITOR     mon(bus, io);
   RAM         #(
                .ROM_START_ADDR(ROM_START_ADDR),
                .ROM_BYTE_SIZE(ROM_BYTE_SIZE),
                .RAM_BYTE_SIZE(RAM_BYTE_SIZE)) ram(bus);

   CPU #(.ID(ID), .VARIANT("CV32E40X")) cpu(bus, io);

   bit use_iss = 0;

   assign bus.Clk = clknrst_if.clk;

   initial begin
      if ($test$plusargs("USE_ISS"))
         use_iss = 1;
   end

   initial begin
     clknrst_if.clk = 1'b0;
      #1;  // time for clknrst_if_dut to set the clk_period
      wait (clk_period != 0.0);
      `uvm_info("OVPWRAP", "Starting OVP clock", UVM_LOW)
      clknrst_if.set_period(clk_period);
      clknrst_if.start_clk();
   end

endmodule : uvmt_cv32e40x_iss_wrap

`endif // __UVMT_CV32E40X_ISS_WRAP_SV__

