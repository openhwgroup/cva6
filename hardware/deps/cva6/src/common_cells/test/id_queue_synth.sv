// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module id_queue_synth (
    input  logic    clk_i,
    input  logic    rst_ni
);

    for (genvar idw = 1; idw < 8; idw++) begin
        typedef logic [idw-1:0] id_t;
        for (genvar cap = 1; cap < 30; cap += 7) begin
            for (genvar dw = 1; dw < 24; dw += 3) begin
                typedef logic [dw-1:0]  data_t;
                typedef logic [dw-1:0]  mask_t;

                id_t    inp_id, oup_id;
                data_t  exists_data, inp_data, oup_data;
                mask_t  exists_mask;
                logic   exists,
                        exists_req, exists_gnt,
                        inp_req,    inp_gnt,
                        oup_data_valid,
                        oup_pop,
                        oup_req,    oup_gnt;

                id_queue #(
                    .ID_WIDTH   (idw),
                    .CAPACITY   (cap),
                    .data_t     (data_t)
                ) i_id_queue (
                    .clk_i              (clk_i),
                    .rst_ni             (rst_ni),
                    .inp_id_i           (inp_id),
                    .inp_data_i         (inp_data),
                    .inp_req_i          (inp_req),
                    .inp_gnt_o          (inp_gnt),
                    .exists_data_i      (exists_data),
                    .exists_mask_i      (exists_mask),
                    .exists_req_i       (exists_req),
                    .exists_o           (exists),
                    .exists_gnt_o       (exists_gnt),
                    .oup_id_i           (oup_id),
                    .oup_pop_i          (oup_pop),
                    .oup_req_i          (oup_req),
                    .oup_data_o         (oup_data),
                    .oup_data_valid_o   (oup_data_valid),
                    .oup_gnt_o          (oup_gnt)
                );
            end
        end
    end

endmodule
