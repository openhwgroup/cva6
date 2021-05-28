// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/// Testbench for Stream Register
module stream_register_tb #(
    parameter type T    = logic[7:0]
);

    logic   clk,
            rst_n,
            clr,
            inp_valid, inp_ready,
            oup_valid, oup_ready;

    T       inp_data,
            oup_data;

    int unsigned nr_checks;

    stream_register #(
        .T  (T)
    ) dut (
        .clk_i      (clk),
        .rst_ni     (rst_n),
        .clr_i      (clr),
        .testmode_i (1'b0),
        .valid_i    (inp_valid),
        .ready_o    (inp_ready),
        .data_i     (inp_data),
        .valid_o    (oup_valid),
        .ready_i    (oup_ready),
        .data_o     (oup_data)
    );

    initial begin
        clk = 1'b0;
        rst_n = 1'b0;
        repeat(8)
            #10ns clk = ~clk;

        rst_n = 1'b1;
        forever
            #10ns clk = ~clk;
    end

    // simulator stopper, this is suboptimal better go for coverage
    initial begin
        #100ms
        $display("Checked %d stimuli", nr_checks);
        $stop;
    end

    class random_action_t;
        rand logic [1:0] action;

        constraint random_action {
            action dist {
                0 := 40,
                1 := 40,
                3 := 2,
                0 := 0
            };
        }
    endclass

    program testbench ();
        logic[7:0] queue [$];
        // clocking outputs are DUT inputs and vice versa
        clocking cb @(posedge clk);
            default input #2 output #4;
            output clr, inp_data, inp_valid, oup_ready;
            input inp_ready, oup_valid, oup_data;
        endclocking

        clocking pck @(posedge clk);
            default input #2 output #4;
            input clr, inp_data, inp_valid, inp_ready, oup_data, oup_valid, oup_ready;
        endclocking

        // --------
        // Driver
        // --------
        initial begin
            automatic random_action_t random_action = new();

            cb.clr <= 1'b0;

            wait (rst_n == 1'b1);
            cb.inp_valid <= 1'b0;

            forever begin
                void'(random_action.randomize());
                repeat($urandom_range(0, 8)) @(cb);
                // $display("%d\n", random_action.action);
                case (random_action.action)
                    0: begin
                        cb.inp_data     <= $urandom_range(0,256);
                        cb.inp_valid    <= 1'b1;
                    end
                    1: begin
                        cb.clr <= 1'b0;
                        cb.inp_data     <= $urandom_range(0,256);
                        cb.inp_valid    <= 1'b0;
                    end
                    default: begin
                        cb.clr          <= 1'b1;
                        cb.inp_valid    <= 1'b0;
                        @(cb);
                        cb.clr          <= 1'b0;
                    end
                endcase
            end
        end

        initial begin
            // wait for reset to be high
            wait (rst_n == 1'b1);
            // pop from queue
            forever begin
                @(cb)
                cb.oup_ready    <= 1'b1;
                repeat($urandom_range(0, 8)) @(cb);
                cb.oup_ready    <= 1'b0;
            end
        end

        // -------------------
        // Monitor && Checker
        // -------------------
        initial begin
            automatic T data;
            nr_checks = 0;
            forever begin
                @(pck)

                if (pck.inp_valid && pck.inp_ready && !pck.clr) begin
                    queue.push_back(pck.inp_data);
                end

                if (pck.oup_valid && pck.oup_ready) begin
                    data = queue.pop_front();
                    // $display("Time: %t, Expected: %0h Got %0h", $time, data, fifo_if.pck.rdata);
                    assert(data == pck.oup_data)
                        else $error("Mismatch, Expected: %0h Got %0h", data, pck.oup_data);
                    nr_checks++;
                end

                if (pck.clr) begin
                    queue = {};
                end

            end
        end
    endprogram

    testbench tb();
endmodule
