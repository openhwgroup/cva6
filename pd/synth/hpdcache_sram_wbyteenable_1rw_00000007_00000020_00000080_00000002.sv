/*
 *  Copyright 2023 Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *  Copyright 2025 Univ. Grenoble Alpes, Inria, TIMA Laboratory
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : March, 2020
 *  Description   : Behavioral model of a 1RW SRAM with write byte enable
 *  History       :
 */
module hpdcache_sram_wbyteenable_1rw_00000007_00000020_00000080_00000002
#(
    parameter int unsigned ADDR_SIZE = 7,
    parameter int unsigned DATA_SIZE = 32,
    parameter int unsigned DEPTH = 2**ADDR_SIZE,
    parameter int unsigned NDATA = 2
)
(
    input  logic                              clk,
    input  logic                              rst_n,
    input  logic                              cs,
    input  logic                              we,
    input  logic [ADDR_SIZE-1:0]              addr,
    input  logic [NDATA-1:0][DATA_SIZE-1:0]   wdata,
    input  logic [NDATA-1:0][DATA_SIZE/8-1:0] wbyteenable,
    output logic [NDATA-1:0][DATA_SIZE-1:0]   rdata
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
                for (int j = 0; j < NDATA; j++) begin
                    for (int i = 0; i < DATA_SIZE/8; i++) begin
                        if (wbyteenable[j][i]) mem[addr][j][i*8 +: 8] <= wdata[j][i*8 +: 8];
                    end
                end
            end else begin
                rdata <= mem[addr];
            end
        end
    end

    //  DPI
    //  {{{
`ifdef HPDCACHE_DPI_ON
    export "DPI-C" task publicSramBeSetMask;
    export "DPI-C" task publicSramBeSetData;

    task automatic publicSramBeSetMask;
        input int index;
        input logic [NDATA-1:0][DATA_SIZE-1:0] mask;
        mem[index] ^= mask;
    endtask

    task automatic publicSramBeSetData;
        input int index;
        input logic [NDATA-1:0][DATA_SIZE-1:0] data;
        mem[index] = data;
    endtask
`endif
    //  }}}
endmodule
// vim: ts=4 : sts=4 : sw=4 : et : tw=100 : spell : spelllang=en
