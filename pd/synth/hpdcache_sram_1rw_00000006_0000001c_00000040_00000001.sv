/*
 *  Copyright 2023 Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *  Copyright 2025 Univ. Grenoble Alpes, Inria, TIMA Laboratory
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : March, 2020
 *  Description   : SRAM behavioral model
 *  History       :
 */
module hpdcache_sram_1rw_00000006_0000001c_00000040_00000001
#(
    parameter int unsigned ADDR_SIZE = 6,
    parameter int unsigned DATA_SIZE = 28,
    parameter int unsigned DEPTH = 2**ADDR_SIZE,
    parameter int unsigned NDATA = 1
)
(
    input  logic                            clk,
    input  logic                            rst_n,
    input  logic                            cs,
    input  logic                            we,
    input  logic [ADDR_SIZE-1:0]            addr,
    input  logic [NDATA-1:0][DATA_SIZE-1:0] wdata,
    output logic [NDATA-1:0][DATA_SIZE-1:0] rdata
);

    /*
     *  Internal memory array declaration
     */
    typedef logic [NDATA-1:0][DATA_SIZE-1:0] mem_t [DEPTH];
    mem_t mem;

    /*
     *  Process to update or read the memory array
     */
    always_ff @(posedge clk)
    begin : mem_update_ff
        if (cs == 1'b1) begin
            if (we == 1'b1) begin
                mem[addr] <= wdata;
            end else begin
                rdata <= mem[addr];
            end
        end
    end : mem_update_ff

    //  DPI
    //  {{{
`ifdef HPDCACHE_DPI_ON
    export "DPI-C" task publicSramSetMask;
    export "DPI-C" task publicSramSetData;

    task automatic publicSramSetMask;
        input int index;
        input logic [NDATA-1:0][DATA_SIZE-1:0] mask;
        mem[index] ^= mask;
    endtask

    task automatic publicSramSetData;
        input int index;
        input logic [NDATA-1:0][DATA_SIZE-1:0] data;
        mem[index] = data;
    endtask
`endif
    //  }}}
endmodule
// vim: ts=4 : sts=4 : sw=4 : et : tw=100 : spell : spelllang=en
