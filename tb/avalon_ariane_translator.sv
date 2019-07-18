/**
 * Translators to translate between ariane's memory interface
 * and Avalon's memory interface
 * 
 */
module avalon_ariane_translator_main (
    // clock and reset
    input logic clock,
    input logic reset_n,
    
    // inputs from ariane:
    input logic        data_req_i,
    input logic        data_we_i,
    input logic [3:0]  data_be_i,
    input logic [31:0] data_addr_i,
    input logic [31:0] data_wdata_i,

    // inputs from avalon slave:
    input logic        avm_main_waitrequest,
    input logic        avm_main_readdatavalid,
    input logic [31:0] avm_main_readdata,
    input logic [1:0]  avm_main_response,


    // outputs for ariane
    output  logic        data_gnt_o,
    output  logic        data_rvalid_o,
    output  logic [31:0] data_rdata_o,
    output  logic        data_err_o, 

    // outputs for avalon slave
    output logic [31:0] avm_main_address,
    output logic [3:0]  avm_main_byteenable,
    output logic        avm_main_read,
    output logic        avm_main_write,
    output logic [31:0] avm_main_writedata
);

    logic write_good;

    always_ff @(posedge clock or negedge reset_n)
        if (!reset_n)
            write_good <= 0;
        else begin
            write_good <= !avm_main_waitrequest && data_req_i && data_we_i;
        end
        
    // error mapping (unused)
    assign data_err_o = |avm_main_response;

    // direct mappings
    assign avm_main_address = data_addr_i;
    assign avm_main_byteenable = data_be_i;
    assign avm_main_writedata = data_wdata_i;
    assign data_rdata_o = avm_main_readdata;

    // nontrivial mappings
    assign avm_main_read = (!data_we_i && data_req_i);
    assign avm_main_write = (data_we_i && data_req_i);

    // weird mappings
    assign data_rvalid_o = avm_main_readdatavalid || write_good;
    assign data_gnt_o = !avm_main_waitrequest && data_req_i;
endmodule // avalon ariane translator (data)



module avalon_ariane_translator_instr (
    // clock and reset
    input  logic clock,
    input  logic reset_n,

    // inputs from ariane
    input  logic        instr_req_i,
    input  logic [31:0] instr_addr_i,

    // inputs from avalon slave
    input  logic [31:0] avm_instr_readdata,
    input  logic        avm_instr_waitrequest,
    input  logic        avm_instr_readdatavalid,


    // outputs for ariane
    output logic        instr_gnt_o,
    output logic        instr_rvalid_o,
    output logic [31:0] instr_rdata_o,

    // outputs for avalon slave
    output logic        avm_instr_read,
    output logic [31:0] avm_instr_address
);

    // TODO remove
    /*
    always_ff @(posedge clock) begin
        if (avm_instr_read) begin
            $display("instruction");
            $display(avm_instr_read);
            $display(avm_instr_readdata);
        end
    end
    */

    // direct mappings
    assign avm_instr_address = instr_addr_i;
    assign avm_instr_read = instr_req_i;
    assign instr_rdata_o = avm_instr_readdata;
    assign instr_rvalid_o = avm_instr_readdatavalid;

    // nontrivial mappings
    assign instr_gnt_o = !avm_instr_waitrequest && instr_req_i;
endmodule
