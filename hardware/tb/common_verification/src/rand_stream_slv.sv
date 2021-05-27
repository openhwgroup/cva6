// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Randomizing Stream (Ready/Valid) Slave
module rand_stream_slv #(
  parameter type  data_t = logic,
  // Minimum number of clock cycles to wait between applying two consecutive values.
  parameter int   MinWaitCycles = -1,
  // Maximum number of clock cycles to wait between applying two consecutive values.
  parameter int   MaxWaitCycles = -1,
  // Application delay: time delay before output changes after an active clock edge.
  parameter time  ApplDelay = 0ps,
  // Acquisition delay: time delay before ready input is read after an active clock edge.
  parameter time  AcqDelay = 0ps,
  // Store each inupt beat in an internal queue.
  parameter bit   Enqueue = 1'b0
) (
  input  logic    clk_i,
  input  logic    rst_ni,

  input  data_t   data_i,
  input  logic    valid_i,
  output logic    ready_o
);

  if (Enqueue) begin: gen_queue
    data_t queue[$];
    always @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        queue = {};
      end else begin
        #(AcqDelay);
        if (valid_i && ready_o) begin
          queue.push_back(data_i);
        end
      end
    end
  end

  rand_synch_driver #(
    .data_t         (logic),
    .MinWaitCycles  (MinWaitCycles),
    .MaxWaitCycles  (MaxWaitCycles),
    .ApplDelay      (ApplDelay)
  ) i_ready_driver (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .data_o (ready_o)
  );

`ifndef VERILATOR
  initial begin: validate_params
    assert (AcqDelay > 0ps)
      else $fatal("The acquisition delay must be greater than 0!");
    assert (AcqDelay > ApplDelay)
      else $fatal("The acquisition delay must be greater than the application delay!");
  end
`endif

endmodule
