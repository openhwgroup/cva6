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

module fmiohmc_ecc_decoder #
    ( parameter
        CFG_ECC_DATA_WIDTH              = 72,
        CFG_ECC_CODE_WIDTH              = 8,
        CFG_ADDR_WIDTH                  = 35,
        
        CFG_PORT_WIDTH_DRAM_DATA_WIDTH  = 7,
        CFG_PORT_WIDTH_LOCAL_DATA_WIDTH = 7,
        CFG_PORT_WIDTH_ENABLE_ECC       = 1,
        
        CFG_ADDR_ENCODE_ENABLED         = 0
    )
    (
        ctl_clk,
        ctl_reset_n,
        
        cfg_local_data_width,
        cfg_dram_data_width,
        cfg_enable_ecc,
        
        input_data,
        input_addr,
        input_data_valid,
        output_data,
        output_data_valid,
        output_ecc_code,
        
        err_corrected,
        err_detected,
        err_fatal,
        err_sbe,
        err_addr_detected,
        err_addr
    );

localparam CFG_LOCAL_DATA_WIDTH = CFG_ECC_DATA_WIDTH - CFG_ECC_CODE_WIDTH;

input                                            ctl_clk;
input                                            ctl_reset_n;

input  [CFG_PORT_WIDTH_DRAM_DATA_WIDTH  - 1 : 0] cfg_local_data_width;
input  [CFG_PORT_WIDTH_LOCAL_DATA_WIDTH - 1 : 0] cfg_dram_data_width;
input  [CFG_PORT_WIDTH_ENABLE_ECC       - 1 : 0] cfg_enable_ecc;

input  [CFG_ECC_DATA_WIDTH              - 1 : 0] input_data;
input  [CFG_ADDR_WIDTH                  - 1 : 0] input_addr;
input                                            input_data_valid;

output [CFG_ECC_DATA_WIDTH              - 1 : 0] output_data;
output                                           output_data_valid;
output [CFG_ECC_CODE_WIDTH              - 1 : 0] output_ecc_code;

output                                           err_corrected;
output                                           err_detected;
output                                           err_fatal;
output                                           err_sbe;
output                                           err_addr_detected;
output [CFG_ADDR_WIDTH                  - 1 : 0] err_addr;

    wire [CFG_ECC_DATA_WIDTH   - 1 : 0] int_decoder_input;
    
    reg  [CFG_ECC_DATA_WIDTH   - 1 : 0] int_decoder_input_data;
    reg  [CFG_ECC_DATA_WIDTH   - 1 : 0] int_decoder_input_ecc_code;
    reg  [CFG_ECC_DATA_WIDTH   - 1 : 0] or_int_decoder_input_ecc_code;
    
    reg  [CFG_ECC_DATA_WIDTH   - 1 : 0] output_data;
    reg                                 output_data_valid;
    reg  [CFG_ECC_CODE_WIDTH   - 1 : 0] output_ecc_code;
    
    reg                                 err_corrected;
    reg                                 err_detected;
    reg                                 err_fatal;
    reg                                 err_sbe;
    reg                                 err_addr_detected;
    reg  [CFG_ADDR_WIDTH       - 1 : 0] err_addr;
    
    wire                                int_err_corrected;
    wire                                int_err_detected;
    wire                                int_err_fatal;
    wire                                int_err_sbe;
    wire                                int_err_addr_detected;
    wire [CFG_ADDR_WIDTH       - 1 : 0] int_err_addr;
    reg  [CFG_ECC_CODE_WIDTH   - 1 : 0] int_output_ecc_code;
    
    wire [CFG_ECC_DATA_WIDTH   - 1 : 0] decoder_input;
    wire [CFG_LOCAL_DATA_WIDTH - 1 : 0] decoder_output;
    reg                                 decoder_output_valid;
    
    wire [CFG_ADDR_WIDTH       - 1 : 0] output_addr;
    
    genvar i;

    generate
        for (i = 0;i < CFG_ECC_DATA_WIDTH;i = i + 1)
        begin : decoder_input_per_data_width
            always @ (*)
            begin
                if (i < cfg_local_data_width)
                    int_decoder_input_data [i] = input_data [i];
                else
                    int_decoder_input_data [i] = 1'b0;
            end
            
            always @ (*)
            begin
                if (i >= cfg_local_data_width && i < cfg_dram_data_width)
                    int_decoder_input_ecc_code [i] = input_data [i];
                else
                    int_decoder_input_ecc_code [i] = 1'b0;
            end
        end
    endgenerate
    
    always @ (*)
    begin
        or_int_decoder_input_ecc_code [CFG_ECC_CODE_WIDTH - 1 : 0] = int_decoder_input_ecc_code [CFG_ECC_CODE_WIDTH - 1 : 0];
    end
    
    generate
        for (i = 1;i < 9;i = i + 1)
        begin : ecc_code_per_code_width
            always @ (*)
            begin
                or_int_decoder_input_ecc_code [(i + 1) * CFG_ECC_CODE_WIDTH - 1 : i * CFG_ECC_CODE_WIDTH      ] =
                int_decoder_input_ecc_code    [(i + 1) * CFG_ECC_CODE_WIDTH - 1 : i * CFG_ECC_CODE_WIDTH      ] |
                or_int_decoder_input_ecc_code [i * CFG_ECC_CODE_WIDTH       - 1 : (i - 1) * CFG_ECC_CODE_WIDTH];
            end
        end
    endgenerate
    
    generate
        if (CFG_ECC_DATA_WIDTH > 72)
        begin
            assign int_decoder_input = {{(CFG_ECC_DATA_WIDTH - 72){1'b0}}, or_int_decoder_input_ecc_code [71 : 64], int_decoder_input_data [63 : 0]}; 
        end
        else
        begin
            assign int_decoder_input = {or_int_decoder_input_ecc_code [71 : 64], int_decoder_input_data [63 : 0]}; 
        end
    endgenerate
    
    assign decoder_input = int_decoder_input;
    
    always @ (*) 
    begin
        decoder_output_valid = input_data_valid;
    end
    
    always @ (*)
    begin
        if (cfg_enable_ecc)
            int_output_ecc_code = or_int_decoder_input_ecc_code [71 : 64]; 
        else
            int_output_ecc_code = {CFG_ECC_CODE_WIDTH{1'b0}};
    end
    
    always @ (*)
    begin
        if (cfg_enable_ecc)
        begin
            output_data = {{CFG_ECC_CODE_WIDTH{1'b0}}, decoder_output}; 
        end
        else
        begin
            output_data = int_decoder_input_data;
        end
        
        if (cfg_enable_ecc)
        begin
            err_corrected       = int_err_corrected;
            err_detected        = int_err_detected;
            err_fatal           = int_err_fatal;
            err_sbe             = int_err_sbe;
            err_addr_detected   = int_err_addr_detected;
            err_addr            = int_err_addr;
        end
        else
        begin
            err_corrected       = 1'b0;
            err_detected        = 1'b0;
            err_fatal           = 1'b0;
            err_sbe             = 1'b0;
            err_addr_detected   = 1'b0;
            err_addr            = {CFG_ADDR_WIDTH{1'b0}};
        end
            
        output_data_valid   = input_data_valid;
        output_ecc_code     = int_output_ecc_code;
    end
    

    
    generate
        if (CFG_LOCAL_DATA_WIDTH > 64)
        begin
            assign decoder_output [CFG_LOCAL_DATA_WIDTH - 1 : 64] = {(CFG_LOCAL_DATA_WIDTH - 64){1'b0}};
        end
    endgenerate
    
    generate
        if (CFG_ADDR_ENCODE_ENABLED == 1)
        begin
            fmiohmc_ecc_decoder_112 #
            (
                .DI                 (72 + CFG_ADDR_WIDTH                                                    ),
                .ADDR               (CFG_ADDR_WIDTH                                                         ),
                .DOUT               (64 + CFG_ADDR_WIDTH                                                    )
            )
            decoder_inst
            (
                .data               ({decoder_input [72 - 1 : 64], input_addr, decoder_input [64 - 1 : 0]}  ),
                .err_corrected      (int_err_corrected                                                      ),
                .err_detected       (int_err_detected                                                       ),
                .err_fatal          (int_err_fatal                                                          ),
                .err_sbe            (int_err_sbe                                                            ),
                .err_addr_detected  (int_err_addr_detected                                                  ),
                .err_addr           (int_err_addr                                                           ),
                .q                  ({output_addr, decoder_output [64 - 1 : 0]}                             )
            );
        end
        else
        begin
            fmiohmc_ecc_decoder_64 decoder_inst
            (
                .data               (decoder_input  [72 - 1 : 0]),
                .err_corrected      (int_err_corrected          ),
                .err_detected       (int_err_detected           ),
                .err_fatal          (int_err_fatal              ),
                .err_sbe            (int_err_sbe                ),
                .q                  (decoder_output [64 - 1 : 0])
            );
            
            assign int_err_addr_detected = 1'b0;
            assign int_err_addr          = {CFG_ADDR_WIDTH{1'b0}};
        end
    endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EAWtIy3hGdLIc4uDo0lbyErkHSivqnASZaK3YwnZhsdx/KE00F8cAu051oZQG7NMqhpwPzgNxes2fNKDntOeA9SlW72axvrVepM/JwIBJUQCllWyr8Km2I6CYsHsHpph7ejHp9P8lI07/hPVVvWEaVzKLfH3LtvQ+N4KvZrweUF5mJKAIf8/L+J75HpEu1e8XguudS29QxKF8sf6p5GcYUxAUqPbYIZ/vMfevXL+WdoINbiimXq+PaDx/2RU+Q4MX/Hiq7IQR67eFuGTk23bXDmJ349NJBlFT+CxvO0dMWB0F9XM1BXBOS/3bD70Sn2t20wdseBO2f1rlj3xXlkbE5g3J487Ef/Eax4ec7/EncMmjszmIimQzXt2qo8MgXLHGnbQj47MCXtg/Ntkd44HyLXGUJY526uNqtGA04Sacwok5KpM6/XRYMUl2kRhwTDOxtmuV3lyfBC/o0Gp59C1s6s+gl0sLko+8xG0iAmZmMkQD2U92LJu/X9K7tpMJRCavnpts3VOaMZQFjRsdG0gn+8Lh6x7JBUfTU30AlgA8nSaQrU2J9Vsw7qFZIgM3nGq7v3JNVms3yGZVpQNijL/fBlnqEivtoHWjpcgT63Cw8QdnAoWtQuK9HN8qvMXdFJ46D7tpHHFcKFq3dPcy2OhPvVmGCAnr++6QRf+UlDFBQB/4BW9EQPmZ6kTLqnXis1bQySaRTrQuuGTG+Gaj63QXR2EtQ5W464m3vfbbicM8n9v33qAtalGU34JIc8+wZ471DCeQiQTlFM1BBv3Gil9m0m"
`endif