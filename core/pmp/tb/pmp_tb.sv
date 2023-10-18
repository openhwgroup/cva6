// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Moritz Schneider, ETH Zurich
// Date: 2.10.2019
// Description: 

import tb_pkg::*;

module pmp_tb;
  timeunit 1ns; timeprecision 1ps;

  localparam int unsigned WIDTH = 16;
  localparam int unsigned PMP_LEN = 13;
  localparam int unsigned NR_ENTRIES = 4;

  logic [WIDTH-1:0] addr;
  riscv::pmp_access_t access_type;

  // Configuration
  logic [NR_ENTRIES-1:0][PMP_LEN-1:0] conf_addr;
  riscv::pmpcfg_t [NR_ENTRIES-1:0] conf;

  // Output
  logic allow;

  // helper signals
  logic [WIDTH-1:0] base;
  int unsigned size;

  pmp #(
      .PLEN(WIDTH),
      .PMP_LEN(PMP_LEN),
      .NR_ENTRIES(NR_ENTRIES)
  ) i_pmp (
      .addr_i       (addr),
      .access_type_i(access_type),
      .priv_lvl_i   (riscv::PRIV_LVL_U),
      .conf_addr_i  (conf_addr),
      .conf_i       (conf),
      .allow_o      (allow)
  );


  initial begin
    // set all pmps to disabled initially
    for (int i = 0; i < NR_ENTRIES; i++) begin
      conf[i].addr_mode = riscv::OFF;
    end

    // test napot 1
    addr = 16'b00011001_10111010;
    access_type = riscv::ACCESS_READ;

    // pmp 3
    base = 16'b00011001_00000000;
    size = 8;
    conf_addr[2] = P#(
        .WIDTH  (WIDTH),
        .PMP_LEN(PMP_LEN)
    )::base_to_conf(
        base, size
    );
    conf[2].addr_mode = riscv::NAPOT;
    conf[2].access_type = riscv::ACCESS_READ | riscv::ACCESS_WRITE | riscv::ACCESS_EXEC;

    #5ns;
    assert (allow == 1);

    // add second PMP entry that disallows

    // pmp 1
    base = 16'b00011001_10110000;
    size = 4;
    conf_addr[1] = P#(
        .WIDTH  (WIDTH),
        .PMP_LEN(PMP_LEN)
    )::base_to_conf(
        base, size
    );
    conf[1].addr_mode = riscv::NAPOT;
    conf[1].access_type = '0;

    #5ns;
    assert (allow == 0);

    // add third PMP entry that allows again

    // pmp 2
    base = 16'b00011001_10111000;
    size = 3;
    conf_addr[0] = P#(
        .WIDTH  (WIDTH),
        .PMP_LEN(PMP_LEN)
    )::base_to_conf(
        base, size
    );
    conf[0].addr_mode = riscv::NAPOT;
    conf[0].access_type = riscv::ACCESS_READ;

    #5ns;
    assert (allow == 1);

  end
endmodule
