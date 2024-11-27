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


// $File: //acds/rel/24.1/ip/iconnect/avalon_st/altera_avalon_dc_fifo/altera_dcfifo_synchronizer_bundle.v $
// $Revision: #1 $
// $Date: 2024/02/01 $
// $Author: psgswbuild $
//-------------------------------------------------------------------------------

`timescale 1 ns / 1 ns
module altera_dcfifo_synchronizer_bundle(
                                     clk,
                                     reset_n,
                                     din,
                                     dout
                                     );
   parameter WIDTH = 1;
   parameter DEPTH = 3;   
   parameter retiming_reg_en = 0;

   input clk;
   input reset_n;
   input [WIDTH-1:0] din;
   output [WIDTH-1:0] dout;
   
   genvar i;
   
   generate
      for (i=0; i<WIDTH; i=i+1)
        begin : sync
           altera_std_synchronizer_nocut #(.depth(DEPTH), .retiming_reg_en(retiming_reg_en))
                                   u (
                                      .clk(clk), 
                                      .reset_n(reset_n), 
                                      .din(din[i]), 
                                      .dout(dout[i])
                                      );
        end
   endgenerate
   
endmodule 

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "oSKThnM8R+v4ntG+2nl4bjKssux9ChPCljWQD7sPiJABKN3SNdkywE5Y9jlQ6S14DWhLDzTra8TiIdkRcVVm742z5SsEdsJozy5YbTTLMwLklS7QykQbr47Q0XEb4wjmHRWxsXN/cqp4yvaj0F/T170jVXGQEeG8jGOUpVeKH05OMFZaeFHtsmfkAiMhLD6Ub4coa1nbk3STuGKv7+r8sFY4IhYpZD54s1pA/oHzEkf5SAwv6fz0dY9ICUe90czvvD6Vi1KwzjX2mtmMNcGZ9wVPIAzRPdF8nCIlC7Bh+F0WgBS1zPPSzxS6ItHFo/ViJOvL1gWkp52tDccHeL8NW+W+wLkWbZVAUDURLcD3CPTi8TDD/sqdokw66lkBYdgdKsq77s2XFi5QOFFfjPM9u1yiyoMRkDAC3AvrNWelZzTmb7qSH9IxezUvRpSt7aW8pOjjOAwkGl48UlGf+32z26cB92EPPYkHXOPqaSDjet4wWkkZBtLEmvC0KDszfN/S2vOasA2n1Wy7MfWPUVCiAz/ELtxkHkzo+ELFz2YPtLAq5T9ZIq2sVAVXrQxvPXHREH+yUHFqzC9yBkIk4EsdZzZw76Gn0cggsXwotUzRzGYSsdhH2XlhvJghWVE/s3IfRXRri24jyuOZ3uPVeHwIGIe3g2D6rMxNr8lIUQRXkcY/A2knnE1ouK7JguFzwFn/Feh2DoL4dL2C5WRbpv1hCKlaXFNEN8xAv/qlTLSB5g/Puvfx7Jg1Ukjj+umRdF5ZRSCIi8Da4igcb/8nuZJhy2fcoDvZgCgYr8EReEIsZXcLaVZm/RH2kx3v4CBZJhJhGGqzCdY+t93JghNQlxwmRn+o7qz19fQjaV+EMdueBcdaLoDetqXe3optoymxRttz3fLl0t0Eh2GqI4v7oKOHFy8YwFT4onVXe7voL83mFXWYOUPR2mQZLIyOH6Qv2FsDt2o5B+AeO8+XKGw5UEk7w3E87eFRYNyAuEPuITrX8FTOfaTIeFAjDwLdyU4KZEHA"
`endif