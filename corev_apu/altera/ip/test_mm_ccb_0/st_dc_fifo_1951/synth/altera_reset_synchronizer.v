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


// $Id: //acds/rel/24.1/ip/iconnect/merlin/altera_reset_controller/altera_reset_synchronizer.v#1 $
// $Revision: #1 $
// $Date: 2024/02/01 $

// -----------------------------------------------
// Reset Synchronizer
// -----------------------------------------------
`timescale 1 ns / 1 ns

module altera_reset_synchronizer
#(
    parameter ASYNC_RESET = 1,
    parameter DEPTH       = 2
)
(
    input   reset_in /* synthesis ALTERA_ATTRIBUTE = "SUPPRESS_DA_RULE_INTERNAL=R101" */,

    input   clk,
    output  reset_out
);

    // -----------------------------------------------
    // Synchronizer register chain. We cannot reuse the
    // standard synchronizer in this implementation 
    // because our timing constraints are different.
    //
    // Instead of cutting the timing path to the d-input 
    // on the first flop we need to cut the aclr input.
    // 
    // We omit the "preserve" attribute on the final
    // output register, so that the synthesis tool can
    // duplicate it where needed.
    // -----------------------------------------------
    (*preserve*) reg [DEPTH-1:0] altera_reset_synchronizer_int_chain;
    reg altera_reset_synchronizer_int_chain_out;

    generate if (ASYNC_RESET) begin

        // -----------------------------------------------
        // Assert asynchronously, deassert synchronously.
        // -----------------------------------------------
        always @(posedge clk or posedge reset_in) begin
            if (reset_in) begin
                altera_reset_synchronizer_int_chain <= {DEPTH{1'b1}};
                altera_reset_synchronizer_int_chain_out <= 1'b1;
            end
            else begin
                altera_reset_synchronizer_int_chain[DEPTH-2:0] <= altera_reset_synchronizer_int_chain[DEPTH-1:1];
                altera_reset_synchronizer_int_chain[DEPTH-1] <= 0;
                altera_reset_synchronizer_int_chain_out <= altera_reset_synchronizer_int_chain[0];
            end
        end

        assign reset_out = altera_reset_synchronizer_int_chain_out;
     
    end else begin

        // -----------------------------------------------
        // Assert synchronously, deassert synchronously.
        // -----------------------------------------------
        always @(posedge clk) begin
            altera_reset_synchronizer_int_chain[DEPTH-2:0] <= altera_reset_synchronizer_int_chain[DEPTH-1:1];
            altera_reset_synchronizer_int_chain[DEPTH-1] <= reset_in;
            altera_reset_synchronizer_int_chain_out <= altera_reset_synchronizer_int_chain[0];
        end

        assign reset_out = altera_reset_synchronizer_int_chain_out;
 
    end
    endgenerate

endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "GdrtC8041f37ha52Ko+Jde808iDyKA+ht5m5AuKQCsm3cRPQscDvF+wBgbawWOxUtCRI9a/tnC6AChwO+BxfmEV2UK9ncMFAL//YMEMfhylNbbg+DkYNRltJ3oLac/x0CKLYUz0kP213IDPHPJdDrn2XWjqkg2d8WjL/DUsL13IJgiL6ltB1LI/UYnSBUYY+yK6OwicfHT3EuyorZ8lWql/zzL2Fl1behLT6A47M1qiV+ysc6vEB01RBKTiwbjjCptsvvyfIUXwKDXLSM2sMa/QCq+rW8aLu8jl/mSGRsu68Nwe2k0nDL0gUkTslUC0BJvgHXm9UW/NFbbYe222vFNdLfPmAkECZUXfB0YU98ztCsOcuJeoGA7tZDBOv25LTHvtId+le8QZjez7iwT7H4ZEoipbUNubNAlRSrCUG+QjXDpIPyNFpL2j2gxSaE8Z2MGBXiI83dupjksBHDZwePQwue3DBacGmRFrfYgzSuxt3l+EG80exhkF/D/mfJAUJEqte04F8q4q/blEJs2ahLbYOW2QktXweWZEzD3Fd6veB9XtGOJ+gptjGA3KwPVyauwd3uSk3BJZXlv1PIak++FFvetBl4XMUN1FgkAijPLg2l1LBPIibpoRCotSmzSyd5vYI+YtYc95sbMSrcIzqiRuqX6rHunhTM419OHmrw5ORhH1jPD2FgiXXUynst6MlICwA7IIpkZNFZ578ztQ9NRIyQYXunh0ZpOTvtSMT5mjd1mF74pslxJYTRDOuiC18Q1o01sLL+DTQxHtOWscMtzpqetyVKhJBWaDGlu/akBtOhm21QV4S3lmFwDmMIevcXw4mSYhiJFeLyA41BpyePHR7are1okO4JY5QFjMY5tWebbIwMVGzgT3YzIzMsThGRd6pOskNHcChwtylGDmyG+hwuW48RcBseRqh32NLlpBIEYsAQcDwSDWloJd4RjMTTYmlTdo76JJqIlS+ymJ+ErmL44RHD7BPvMYXxaEVDzV9L/3Qe7dDZ7PC7CYNTbXY"
`endif