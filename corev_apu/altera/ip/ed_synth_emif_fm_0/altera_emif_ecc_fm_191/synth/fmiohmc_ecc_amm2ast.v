// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.



`timescale 1 ps / 1 ps

module fmiohmc_ecc_amm2ast #
    ( parameter
        CFG_LOCAL_SIZE_WIDTH    = 2
    )
    (
        clk,
        reset_n,
        amm_ready,
        amm_cmd_size,
        amm_cmd_wr,
        amm_cmd_rd,
        ast_cmd_ready,
        ast_cmd_valid,
        ast_wr_data_ready,
        ast_wr_data_valid
    );

localparam IDLE      = 1'b0;
localparam GET_WDATA = 1'b1;

input                                clk;
input                                reset_n;

output                               amm_ready;
input [CFG_LOCAL_SIZE_WIDTH - 1 : 0] amm_cmd_size;
input                                amm_cmd_wr;
input                                amm_cmd_rd;

input                                ast_cmd_ready;
output                               ast_cmd_valid;
input                                ast_wr_data_ready;
output                               ast_wr_data_valid;

reg                                  int_amm_ready;
reg                                  int_ast_wr_data_valid;
reg                                  int_ast_cmd_valid;

reg                                  convert_state;
reg                                  convert_state_nxt;
reg  [CFG_LOCAL_SIZE_WIDTH - 1 : 0]  count;
reg  [CFG_LOCAL_SIZE_WIDTH - 1 : 0]  count_nxt;

wire                                 ast_cmd_valid;
wire                                 ast_wr_data_valid;
wire                                 amm_ready;


always @(*)
begin
    case (convert_state)
    IDLE:
        begin
            int_amm_ready     = ast_wr_data_ready & ast_cmd_ready;
            int_ast_cmd_valid = (amm_cmd_wr | amm_cmd_rd) & ast_wr_data_ready & ast_cmd_ready; 
            
            if (amm_cmd_wr)
            begin
                if (amm_cmd_size != {{(CFG_LOCAL_SIZE_WIDTH - 1){1'b0}},1'b1})
                    begin
                        if (int_amm_ready == 1'b1)
                        begin
                            convert_state_nxt    = GET_WDATA;
                            count_nxt            = amm_cmd_size;
                            int_ast_wr_data_valid = 1'b1;
                        end
                        else
                        begin
                            convert_state_nxt    = IDLE;
                            count_nxt            = {CFG_LOCAL_SIZE_WIDTH{1'b0}};
                            int_ast_wr_data_valid = 1'b0;
                        end
                    end
                else
                begin
                    count_nxt         = {CFG_LOCAL_SIZE_WIDTH{1'b0}};
                    convert_state_nxt = IDLE;
                    
                    if (int_amm_ready == 1'b1)
                    begin
                        int_ast_wr_data_valid = 1'b1;
                    end
                    else
                    begin
                        int_ast_wr_data_valid = 1'b0;
                    end
                end
            end
            else
            begin
                if (amm_cmd_rd == 1'b1)
                begin
                    int_ast_wr_data_valid = 1'b0;
                    count_nxt            = {CFG_LOCAL_SIZE_WIDTH{1'b0}};
                    convert_state_nxt    = IDLE;
                end
                else
                begin
                    int_ast_wr_data_valid = 1'b0;
                    count_nxt            = {CFG_LOCAL_SIZE_WIDTH{1'b0}};
                    convert_state_nxt    = IDLE;
                end
            end
        end
    GET_WDATA:
        begin
            int_amm_ready     = ast_wr_data_ready;
            int_ast_cmd_valid = 1'b0;
            
            if (int_amm_ready == 1'b1)
            begin
                if (amm_cmd_wr)
                begin
                    count_nxt            = count - {{(CFG_LOCAL_SIZE_WIDTH - 1){1'b0}},1'b1};
                    int_ast_wr_data_valid = 1'b1;
                end
                else
                begin
                    count_nxt            = count;
                    int_ast_wr_data_valid = 1'b0;
                end
                
                if ((count == {{(CFG_LOCAL_SIZE_WIDTH-2){1'b0}},2'b10}) && (amm_cmd_wr == 1'b1))
                begin
                    convert_state_nxt = IDLE;
                end
                else
                begin
                    convert_state_nxt = GET_WDATA;
                end
            end
            else
            begin
               convert_state_nxt    = GET_WDATA;
               count_nxt            = count;
               int_ast_wr_data_valid = 1'b0;
            end
        end
    endcase
end

always @(posedge clk)
begin
    if (!reset_n)
    begin
        convert_state <= IDLE;
    end
    else begin
        convert_state <= convert_state_nxt;
    end
end

always @(posedge clk)
begin
    count <= count_nxt;
end


assign amm_ready         = int_amm_ready;
assign ast_wr_data_valid = int_ast_wr_data_valid;
assign ast_cmd_valid     = int_ast_cmd_valid;

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EDJKkf0NswlJB1vf587smpPbIBhSkXx1z3ffv5cRb9HXl9SopMPG9vpzWQo6XWMFLQ3uPpPv+jtNALNVw+JXfZ+1H3WW5mhsuFDl7ieIuSnGrSDMo3coAFqZN4Xi3FAZdVQycP3imHGPy7g3gYUqsqbrUKoYbvkFQ4ao5Itr6mIqeZVW5VATTjs0BYvGyI8b8G6IrS6AIWXRZB+Z9laPhvZsV816XG6M75XB8Kx9VNpgfVPXFdqhbLk0KblbB7SPM5DFn5we8bYA2bIPFZ2QQtPpawsCStHyaS7VFzARovJqXODZmqFTbuHSETSoWCydU3gGTLnXokjEDgr20Tu+LmwYefdCr8cecLT8xGVUWACyTIvnl2CpQ1J9YG/k8VUpFL2qh6Lobsp0J7F60z8JeyYjhemH1ZfTgy38vdYOS3TQijS9IddTzbJP9xlic12M3ZI6rn7WQkr2kkzJLrn6nQZoyTeW6glf92aLQ9ZJIlzC4W5ihe8uA/ojMhTxuf3I1a/SVIeS/gd5CQlmu0qhyWX4FipF9OB9j121OgZi9Nei0PK34ayrfAJfrP4HlBUdoea6qzn1+6quFVdNH/mu2VajDOyOvN2ewwkrq7LH+0NE7jDYtEjK3LN49S667PwFcmCtzVFD047++35n4iIApJCnQMW+nwrj4X1yS6LV+vJvijhZ4sO7oEV3G5cc+r02qgpr4TJgQ8XKWH9zn0Ix/k/LqL+i7bIfjZYyNpX9Msrg/iFmJUf9jtjJUWNLx+jBj0ReFTOjkbITQPhBB/8w/Fy"
`endif