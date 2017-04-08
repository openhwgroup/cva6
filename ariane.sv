/* Ariane Top-level module
 * File:   scoreboard.sv
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   19.3.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 */
import ariane_pkg::*;

module ariane
    #(
        parameter N_EXT_PERF_COUNTERS = 0,
        parameter INSTR_RDATA_WIDTH   = 64
    )
    (
        input  logic                           clk_i,
        input  logic                           rst_n,
        input  logic                           clock_en_i,    // enable clock, otherwise it is gated
        input  logic                           test_en_i,     // enable all clock gates for testing

        // CPU Control Signals
        input  logic                           fetch_enable_i,
        output logic                           core_busy_o,
        input  logic [N_EXT_PERF_COUNTERS-1:0] ext_perf_counters_i,

        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [64:0]                    boot_addr_i,
        input  logic [ 3:0]                    core_id_i,
        input  logic [ 5:0]                    cluster_id_i,
        // Instruction memory interface
        mem_if.Slave                           instr_if,

        // Data memory interface
        mem_if.Slave                           data_if,

        // Interrupt inputs
        input  logic                           irq_i,                 // level sensitive IR lines
        input  logic [4:0]                     irq_id_i,
        output logic                           irq_ack_o,
        input  logic                           irq_sec_i,
        output logic                           sec_lvl_o,

        // Debug Interface
        debug_if.Slave                         debug_if
    );




endmodule // ariane