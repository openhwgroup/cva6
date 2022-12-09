// Copyright 2018, 2021 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Stefan Mach <smach@iis.ee.ethz.ch>
// Description: Common register defines for RTL designs

`ifndef COMMON_CELLS_REGISTERS_SVH_
`define COMMON_CELLS_REGISTERS_SVH_

// Abridged Summary of available FF macros:
// `FF:      asynchronous active-low reset
// `FFAR:    asynchronous active-high reset
// `FFARN:   [deprecated] asynchronous active-low reset
// `FFSR:    synchronous active-high reset
// `FFSRN:   synchronous active-low reset
// `FFNR:    without reset
// `FFL:     load-enable and asynchronous active-low reset
// `FFLAR:   load-enable and asynchronous active-high reset
// `FFLARN:  [deprecated] load-enable and asynchronous active-low reset
// `FFLARNC: load-enable and asynchronous active-low reset and synchronous active-high clear
// `FFLSR:   load-enable and synchronous active-high reset
// `FFLSRN:  load-enable and synchronous active-low reset
// `FFLNR:   load-enable without reset

`ifdef VERILATOR
`define NO_SYNOPSYS_FF 1
`endif

`define REG_DFLT_CLK clk_i
`define REG_DFLT_RST rst_ni

// Flip-Flop with asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// (__clk: clock input)
// (__arst_n: asynchronous reset, active-low)
`define FF(__q, __d, __reset_value, __clk = `REG_DFLT_CLK, __arst_n = `REG_DFLT_RST) \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin                           \
    if (!__arst_n) begin                                                             \
      __q <= (__reset_value);                                                        \
    end else begin                                                                   \
      __q <= (__d);                                                                  \
    end                                                                              \
  end

// Flip-Flop with asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFAR(__q, __d, __reset_value, __clk, __arst)     \
  always_ff @(posedge (__clk) or posedge (__arst)) begin \
    if (__arst) begin                                    \
      __q <= (__reset_value);                            \
    end else begin                                       \
      __q <= (__d);                                      \
    end                                                  \
  end

// DEPRECATED - use `FF instead
// Flip-Flop with asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFARN(__q, __d, __reset_value, __clk, __arst_n) \
  `FF(__q, __d, __reset_value, __clk, __arst_n)

// Flip-Flop with synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFSR(__q, __d, __reset_value, __clk, __reset_clk) \
  `ifndef NO_SYNOPSYS_FF                       \
  /``* synopsys sync_set_reset `"__reset_clk`" *``/       \
    `endif                        \
  always_ff @(posedge (__clk)) begin                      \
    __q <= (__reset_clk) ? (__reset_value) : (__d);       \
  end

// Flip-Flop with synchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFSRN(__q, __d, __reset_value, __clk, __reset_n_clk) \
    `ifndef NO_SYNOPSYS_FF                       \
  /``* synopsys sync_set_reset `"__reset_n_clk`" *``/        \
    `endif                        \
  always_ff @(posedge (__clk)) begin                         \
    __q <= (!__reset_n_clk) ? (__reset_value) : (__d);       \
  end

// Always-enable Flip-Flop without reset
// __q: Q output of FF
// __d: D input of FF
// __clk: clock input
`define FFNR(__q, __d, __clk)        \
  always_ff @(posedge (__clk)) begin \
    __q <= (__d);                    \
  end

// Flip-Flop with load-enable and asynchronous active-low reset (implicit clock and reset)
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// (__clk: clock input)
// (__arst_n: asynchronous reset, active-low)
`define FFL(__q, __d, __load, __reset_value, __clk = `REG_DFLT_CLK, __arst_n = `REG_DFLT_RST) \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin                                    \
    if (!__arst_n) begin                                                                      \
      __q <= (__reset_value);                                                                 \
    end else begin                                                                            \
      __q <= (__load) ? (__d) : (__q);                                                        \
    end                                                                                       \
  end

// Flip-Flop with load-enable and asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset, active-high
`define FFLAR(__q, __d, __load, __reset_value, __clk, __arst) \
  always_ff @(posedge (__clk) or posedge (__arst)) begin      \
    if (__arst) begin                                         \
      __q <= (__reset_value);                                 \
    end else begin                                            \
      __q <= (__load) ? (__d) : (__q);                        \
    end                                                       \
  end

// DEPRECATED - use `FFL instead
// Flip-Flop with load-enable and asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLARN(__q, __d, __load, __reset_value, __clk, __arst_n) \
  `FFL(__q, __d, __load, __reset_value, __clk, __arst_n)

// Flip-Flop with load-enable and synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input, active-high
`define FFLSR(__q, __d, __load, __reset_value, __clk, __reset_clk)       \
    `ifndef NO_SYNOPSYS_FF                                               \
  /``* synopsys sync_set_reset `"__reset_clk`" *``/                      \
    `endif                                                               \
  always_ff @(posedge (__clk)) begin                                     \
    __q <= (__reset_clk) ? (__reset_value) : ((__load) ? (__d) : (__q)); \
  end

// Flip-Flop with load-enable and synchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_n_clk: reset input, active-low
`define FFLSRN(__q, __d, __load, __reset_value, __clk, __reset_n_clk)       \
    `ifndef NO_SYNOPSYS_FF                                                  \
  /``* synopsys sync_set_reset `"__reset_n_clk`" *``/                       \
    `endif                                                                  \
  always_ff @(posedge (__clk)) begin                                        \
    __q <= (!__reset_n_clk) ? (__reset_value) : ((__load) ? (__d) : (__q)); \
  end

// Flip-Flop with load-enable and asynchronous active-low reset and synchronous clear
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __clear: assign reset value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset, active-low
`define FFLARNC(__q, __d, __load, __clear, __reset_value, __clk, __arst_n) \
    `ifndef NO_SYNOPSYS_FF                                                 \
  /``* synopsys sync_set_reset `"__clear`" *``/                            \
    `endif                                                                 \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin                 \
    if (!__arst_n) begin                                                   \
      __q <= (__reset_value);                                              \
    end else begin                                                         \
      __q <= (__clear) ? (__reset_value) : (__load) ? (__d) : (__q);       \
    end                                                                    \
  end

// Load-enable Flip-Flop without reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __clk: clock input
`define FFLNR(__q, __d, __load, __clk) \
  always_ff @(posedge (__clk)) begin   \
    __q <= (__load) ? (__d) : (__q);   \
  end

`endif
