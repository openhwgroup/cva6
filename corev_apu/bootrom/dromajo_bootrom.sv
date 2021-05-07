/* Copyright 2020 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File: dromajo_bootrom.sv
 *
 * Author: Nursultan Kabylkas, UCSC
 * Description: bootrom that gets synced with dromajo for
 * cosimulation purposes.
 */

module dromajo_bootrom (
   input  logic         clk_i,
   input  logic         req_i,
   input  logic [63:0]  addr_i,
   output logic [63:0]  rdata_o
);
    localparam int RomSize = 4096;
    logic [63:0] mem[RomSize-1:0];

    initial begin
      integer hex_file, num_bytes;
      longint address, value;
      string f_name;
      // init to 0
      for (int k=0; k<RomSize; k++) begin
        mem[k] = 0;
      end

      // sync with dromajo
      if ($value$plusargs("checkpoint=%s", f_name)) begin
        hex_file = $fopen({f_name,".bootram.hex"}, "r");
        while (!$feof(hex_file)) begin
          num_bytes = $fscanf(hex_file, "%d %h\n", address, value);
          //$display("%d %h", address, value);
          mem[address] = value;
        end
        $display("Done syncing boot ROM with dromajo...\n");
      end else begin
        $display("Failed syncing boot ROM: provide path to a checkpoint.\n");
      end

    end

    logic [$clog2(RomSize)-1:0] addr_q;

    always_ff @(posedge clk_i) begin
        if (req_i) begin
            addr_q <= addr_i[$clog2(RomSize)-1+3:3];
        end
    end

    // this prevents spurious Xes from propagating into
    // the speculative fetch stage of the core
    assign rdata_o = (addr_q < RomSize) ? mem[addr_q] : '0;
endmodule
