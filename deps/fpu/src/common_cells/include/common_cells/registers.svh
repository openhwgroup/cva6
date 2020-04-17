// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Common register defines for RTL designs
`ifndef COMMON_CELLS_REGISTERS_SVH_
`define COMMON_CELLS_REGISTERS_SVH_

// Abridged Summary of available FF macros:
// `FF:      asynchronous active-low reset (implicit clock and reset)
// `FFAR:    asynchronous active-high reset
// `FFARN:   asynchronous active-low reset
// `FFSR:    synchronous active-high reset
// `FFSRN:   synchronous active-low reset
// `FFNR:    without reset
// `FFL:     load-enable and asynchronous active-low reset (implicit clock and reset)
// `FFLAR:   load-enable and asynchronous active-high reset
// `FFLARN:  load-enable and asynchronous active-low reset
// `FFLARNC: load-enable and asynchronous active-low reset and synchronous active-high clear
// `FFLSR:   load-enable and synchronous active-high reset
// `FFLSRN:  load-enable and synchronous active-low reset
// `FFLNR:   load-enable without reset


// Flip-Flop with asynchronous active-low reset (implicit clock and reset)
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// Implicit:
// clk_i: clock input
// rst_ni: reset input (asynchronous, active low)
`define FF(__q, __d, __reset_value)                  \
  always_ff @(posedge clk_i or negedge rst_ni) begin \
    if (!rst_ni) begin                               \
      __q <= (__reset_value);                        \
    end else begin                                   \
      __q <= (__d);                                  \
    end                                              \
  end

// Flip-Flop with asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset
`define FFAR(__q, __d, __reset_value, __clk, __arst)     \
  always_ff @(posedge (__clk) or posedge (__arst)) begin \
    if (__arst) begin                                    \
      __q <= (__reset_value);                            \
    end else begin                                       \
      __q <= (__d);                                      \
    end                                                  \
  end

// Flip-Flop with asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset
`define FFARN(__q, __d, __reset_value, __clk, __arst_n)    \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin \
    if (!__arst_n) begin                                   \
      __q <= (__reset_value);                              \
    end else begin                                         \
      __q <= (__d);                                        \
    end                                                    \
  end

// Flip-Flop with synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input
`define FFSR(__q, __d, __reset_value, __clk, __reset_clk) \
  `ifndef VERILATOR                       \
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
// __reset_n_clk: reset input
`define FFSRN(__q, __d, __reset_value, __clk, __reset_n_clk) \
    `ifndef VERILATOR                       \
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
// Implicit:
// clk_i: clock input
// rst_ni: reset input (asynchronous, active low)
`define FFL(__q, __d, __load, __reset_value)         \
  always_ff @(posedge clk_i or negedge rst_ni) begin \
    if (!rst_ni) begin                               \
      __q <= (__reset_value);                        \
    end else begin                                   \
      __q <= (__load) ? (__d) : (__q);               \
    end                                              \
  end

// Flip-Flop with load-enable and asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset
`define FFLAR(__q, __d, __load, __reset_value, __clk, __arst) \
  always_ff @(posedge (__clk) or posedge (__arst)) begin      \
    if (__arst) begin                                         \
      __q <= (__reset_value);                                 \
    end else begin                                            \
      __q <= (__load) ? (__d) : (__q);                        \
    end                                                       \
  end

// Flip-Flop with load-enable and asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset
`define FFLARN(__q, __d, __load, __reset_value, __clk, __arst_n) \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin       \
    if (!__arst_n) begin                                         \
      __q <= (__reset_value);                                    \
    end else begin                                               \
      __q <= (__load) ? (__d) : (__q);                           \
    end                                                          \
  end

// Flip-Flop with load-enable and synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input
`define FFLSR(__q, __d, __load, __reset_value, __clk, __reset_clk)       \
    `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__reset_clk`" *``/                      \
    `endif                        \
  always_ff @(posedge (__clk)) begin                                     \
    __q <= (__reset_clk) ? (__reset_value) : ((__load) ? (__d) : (__q)); \
  end

// Flip-Flop with load-enable and synchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_n_clk: reset input
`define FFLSRN(__q, __d, __load, __reset_value, __clk, __reset_n_clk)       \
    `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__reset_n_clk`" *``/                       \
    `endif                        \
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
// __arst_n: asynchronous reset
`define FFLARNC(__q, __d, __load, __clear, __reset_value, __clk, __arst_n) \
    `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__clear`" *``/                       \
    `endif                        \
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
