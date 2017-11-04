// Author: Florian Zaruba, ETH Zurich
// Date: 13.10.2017
// Description: SRAM Behavioral Model
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.

module sram #(
    int unsigned DATA_WIDTH = 64,
    int unsigned NUM_WORDS  = 1024
)(
   input  logic                          clk_i,

   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [DATA_WIDTH-1:0]         be_i,
   output logic [DATA_WIDTH-1:0]         rdata_o
);

    generate
        if (NUM_WORDS == 256) begin
            if (DATA_WIDTH == 16) begin
                IN22FDX_R1PH_NFHN_W00256B016M02C256 dirtyram (
                 .CLK           ( clk_i       ),
                 .CEN           ( ~req_i      ),
                 .RDWEN         ( ~we_i       ),
                 .AW            ( addr_i[7:1] ),
                 .AC            ( addr_i[0]   ),
                 .D             ( wdata_i     ),
                 .BW            ( ~be_i       ),
                 .T_LOGIC       ( 1'b0        ),
                 .MA_SAWL       ( '0          ),
                 .MA_WL         ( '0          ),
                 .MA_WRAS       ( '0          ),
                 .MA_WRASD      ( '0          ),
                 .Q             ( rdata_o     ),
                 .OBSV_CTL      (             )
                );
            end

            if (DATA_WIDTH == 44) begin
                logic [45:0] rdata;
                assign rdata_o = rdata[43:0];

                IN22FDX_R1PH_NFHN_W00256B046M02C256 TAG_RAM  (
                    .CLK         ( clk_i           ),
                    .CEN         ( ~req_i          ),
                    .RDWEN       ( ~we_i           ),
                    .AW          ( addr_i[7:1]     ),
                    .AC          ( addr_i[0]       ),
                    .D           ( {2'b0, wdata_i} ),
                    .BW          ( {2'b0, be_i }   ),
                    .T_LOGIC     ( 1'b0            ),
                    .MA_SAWL     ( '0              ),
                    .MA_WL       ( '0              ),
                    .MA_WRAS     ( '0              ),
                    .MA_WRASD    ( '0              ),
                    .Q           ( rdata           ),
                    .OBSV_CTL    (                 )
                 );
            end

            if (DATA_WIDTH == 128) begin
                IN22FDX_R1PH_NFHN_W00256B128M02C256 DATA_RAM
                  (
                   .CLK           ( clk_i       ),
                   .CEN           ( ~req_i      ),
                   .RDWEN         ( ~we_i       ),
                   .AW            ( addr_i[7:1] ),
                   .AC            ( addr_i[0]   ),
                   .D             ( wdata_i     ),
                   .BW            ( be_i        ),
                   .T_LOGIC       ( 1'b0        ),
                   .MA_SAWL       ( '0          ),
                   .MA_WL         ( '0          ),
                   .MA_WRAS       ( '0          ),
                   .MA_WRASD      ( '0          ),
                   .Q             ( rdata_o     ),
                   .OBSV_CTL      (             )
                );
            end
        end
    endgenerate

endmodule
