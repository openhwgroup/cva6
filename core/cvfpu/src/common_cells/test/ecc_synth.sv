// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module ecc_synth;

    for (genvar dw = 8; dw < 32; dw += 8) begin
        // codeword + parity bit
        logic [ecc_pkg::get_cw_width(dw)-1:0] codeword;
        ecc_encode #(.DataWidth(dw)) i_encode (.data_i(), .data_o(codeword));
        ecc_decode #(.DataWidth(dw))
        i_decode (
            .data_i (codeword),
            .data_o (),
            .syndrome_o (),
            .single_error_o (),
            .double_error_o ()
        );
    end

endmodule
