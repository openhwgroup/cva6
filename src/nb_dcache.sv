
import ariane_pkg::*;

module nb_dcache (
    input logic                   clk_i,    // Clock
    input logic                   rst_ni,   // Asynchronous reset active low
    // AXI refill port
    AXI_BUS.Master                data_if,
    // AMO interface
    input  logic                  amo_commit_i, // commit atomic memory operation
    output logic                  amo_valid_o,  // we have a valid AMO result
    output logic [63:0]           amo_result_o, // result of atomic memory operation
    // Request ports
    input  logic [2:0][11:0]      address_index_i,
    input  logic [2:0][43:0]      address_tag_i,
    input  logic [2:0][63:0]      data_wdata_i,
    input  logic [2:0]            data_req_i,
    input  logic [2:0]            data_we_i,
    input  logic [2:0][7:0]       data_be_i,
    input  logic [2:0]            kill_req_i,
    input  logic [2:0]            tag_valid_i,
    output logic [2:0]            data_gnt_o,
    output logic [2:0]            data_rvalid_o,
    output logic [2:0][63:0]      data_rdata_o,
    input  amo_t [2:0]            amo_op_i
);
    // AMO ALU


    // Cache FSM


    // Memories


    // AXI Module

`ifndef SYNTHESIS
    initial begin
        assert ($bits(data_if.aw_addr) == 64) else $fatal(1, "Ariane needs a 64-bit bus");
    end
`endif
endmodule
