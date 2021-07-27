// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>


/// A connector that joins two AXI-Lite interfaces.
module axi_lite_join (
    AXI_LITE.Slave  in,
    AXI_LITE.Master out
);

    `ifndef SYNTHESIS
    initial begin
        assert(in.AXI_ADDR_WIDTH == out.AXI_ADDR_WIDTH);
        assert(in.AXI_DATA_WIDTH == out.AXI_DATA_WIDTH);
    end
    `endif

    assign out.aw_addr   = in.aw_addr;
    assign out.aw_valid  = in.aw_valid;
    assign out.w_data    = in.w_data;
    assign out.w_strb    = in.w_strb;
    assign out.w_valid   = in.w_valid;
    assign out.b_ready   = in.b_ready;
    assign out.ar_addr   = in.ar_addr;
    assign out.ar_valid  = in.ar_valid;
    assign out.r_ready   = in.r_ready;

    assign in.aw_ready = out.aw_ready;
    assign in.w_ready  = out.w_ready;
    assign in.b_resp   = out.b_resp;
    assign in.b_valid  = out.b_valid;
    assign in.ar_ready = out.ar_ready;
    assign in.r_data   = out.r_data;
    assign in.r_resp   = out.r_resp;
    assign in.r_valid  = out.r_valid;

endmodule
