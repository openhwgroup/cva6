// Copyright 2020 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// Stream test package containing drivers and common definitions for the
/// stream interface.
package stream_test;

  class stream_driver #(
    /// Payload data type.
    parameter type payload_t = logic,
    /// Stimuli application time.
    parameter time TA = 2ns,
    /// Stimuli test time.
    parameter time TT = 8ns
  );
    virtual STREAM_DV #(
      .payload_t (payload_t)
    ) stream;

    function new (
      virtual STREAM_DV #(
        .payload_t (payload_t)
      ) stream
    );
      this.stream = stream;
    endfunction

    function void reset_in();
      stream.valid = 1'b0;
    endfunction

    function void reset_out();
      stream.ready = 1'b0;
    endfunction

    task automatic cycle_start;
      #TT;
    endtask

    task automatic cycle_end;
      @(posedge stream.clk_i);
    endtask

    /// Send a packet on the stream interface.
    task automatic send (input payload_t data);
      stream.data  <= #TA data;
      stream.valid <= #TA 1'b1;
      cycle_start();
      while (stream.ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      stream.valid <= #TA 1'b0;
    endtask

    /// Receive a packet on the stream interface.
    task automatic recv(output payload_t data);
      stream.ready <= #TA 1'b1;
      cycle_start();
      while (stream.valid != 1) begin cycle_end(); cycle_start(); end
      data = stream.data;
      cycle_end();
      stream.ready <= #TA 1'b0;
    endtask
  endclass
endpackage
