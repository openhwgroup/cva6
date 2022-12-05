// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module id_queue_tb #(
    parameter int ID_WIDTH = 10,
    parameter int CAPACITY = 30,
    parameter int unsigned INP_MIN_WAIT_CYCLES = 0,
    parameter int unsigned INP_MAX_WAIT_CYCLES = 40,
    parameter int unsigned OUP_MIN_WAIT_CYCLES = 0,
    parameter int unsigned OUP_MAX_WAIT_CYCLES = INP_MAX_WAIT_CYCLES/2,
    parameter int unsigned N_CHECKS = 10000,
    parameter bit VERBOSE = 1'b0,
    parameter type data_t = logic[3:0]
);

    localparam time TCLK = 10ns;
    localparam time TA = TCLK * 1/4;
    localparam time TT = TCLK * 3/4;

    typedef logic [ID_WIDTH-1:0] id_t;
    typedef logic [$bits(data_t)-1:0] mask_t;

    typedef struct packed {
        id_t    id;
        data_t  data;
    } queue_t;

    typedef struct packed {
        data_t  data;
        mask_t  mask;
    } exists_t;

    logic       clk,
                rst_n;

    data_t      inp_data,
                oup_data;

    exists_t    exists_inp;

    id_t        inp_id,
                oup_id;

    queue_t     queue_inp;

    logic       exists,
                exists_req,         exists_gnt,
                inp_req,            inp_gnt,
                oup_req,            oup_gnt,
                oup_pop,
                oup_data_valid;

    clk_rst_gen #(
        .ClkPeriod    (TCLK),
        .RstClkCycles (5)
    ) i_clk_rst_gen (
        .clk_o  (clk),
        .rst_no (rst_n)
    );

    id_queue #(
        .ID_WIDTH   (ID_WIDTH),
        .CAPACITY   (CAPACITY),
        .data_t     (data_t)
    ) dut (
        .clk_i              (clk),
        .rst_ni             (rst_n),

        .inp_id_i           (inp_id),
        .inp_data_i         (inp_data),
        .inp_req_i          (inp_req),
        .inp_gnt_o          (inp_gnt),

        .exists_data_i      (exists_inp.data),
        .exists_mask_i      (exists_inp.mask),
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

    // Random Input Driver
    rand_stream_mst #(
        .data_t             (queue_t),
        .MinWaitCycles      (INP_MIN_WAIT_CYCLES),
        .MaxWaitCycles      (INP_MAX_WAIT_CYCLES),
        .ApplDelay          (TA),
        .AcqDelay           (TT)
    ) i_inp_mst (
        .clk_i      (clk),
        .rst_ni     (rst_n),

        .data_o     (queue_inp),
        .valid_o    (inp_req),
        .ready_i    (inp_gnt)
    );
    assign inp_id   = queue_inp.id;
    assign inp_data = queue_inp.data;

    // Random Output Driver
    rand_stream_mst #(
        .data_t             (logic),
        .MinWaitCycles      (OUP_MIN_WAIT_CYCLES),
        .MaxWaitCycles      (OUP_MAX_WAIT_CYCLES),
        .ApplDelay          (TA),
        .AcqDelay           (TT)
    ) i_oup_mst (
        .clk_i      (clk),
        .rst_ni     (rst_n),

        .data_o     (),
        .valid_o    (oup_req),
        .ready_i    (oup_gnt)
    );

    // Random Exists Driver
    rand_stream_mst #(
        .data_t             (exists_t),
        .MinWaitCycles      (OUP_MIN_WAIT_CYCLES),
        .MaxWaitCycles      (OUP_MAX_WAIT_CYCLES),
        .ApplDelay          (TA),
        .AcqDelay           (TT)
    ) i_exists_mst (
        .clk_i      (clk),
        .rst_ni     (rst_n),

        .data_o     (exists_inp),
        .valid_o    (exists_req),
        .ready_i    (exists_gnt)
    );

    // Model expected state of queue.
    import rand_id_queue_pkg::*;
    rand_id_queue #(
        .data_t     (data_t),
        .ID_WIDTH   (ID_WIDTH)
    ) exp_queue = new;
    initial begin
        wait (rst_n);
        forever begin
            @(posedge clk);
            if (inp_req && inp_gnt) begin
                exp_queue.push(inp_id, inp_data);
                if (VERBOSE) begin
                    $display("%0t: new entry %0x at ID %0x", $time, inp_data, inp_id);
                end
            end
            if (oup_req && oup_gnt && oup_pop) begin
                if (VERBOSE) begin
                    $display("%0t: removed entry from ID %0x", $time, oup_id);
                end
                void'(exp_queue.pop_id(oup_id));
            end
        end
    end

    // Check the output of the ID queues.
    initial begin
        wait (rst_n);
        forever begin
            @(posedge clk);
            #(TT);
            if (exists_req && exists_gnt) begin
                automatic logic match = 1'b0;
                automatic mask_t mask = exists_inp.mask;
                automatic data_t masked_exists = exists_inp.data & mask;
                for (int unsigned id = 0; id < 2**ID_WIDTH; id++) begin
                    for (int unsigned idx = 0; idx < exp_queue.queues[id].size(); idx++) begin
                        match = ((exp_queue.queues[id][idx] & mask) == masked_exists);
                        if (match) begin
                            break;
                        end
                    end
                    if (match) begin
                        break;
                    end
                end
                assert (exists == match) else begin
                    if (match) begin
                        $error("Entry with value %0x and mask %0b should exist but ID queue did not find it!",
                            exists_inp.data, exists_inp.mask);
                    end else begin
                        $error("Entry with value %0x and mask %0b should NOT exist but ID queue found it!",
                            exists_inp.data, exists_inp.mask);
                    end
                end
            end
            if (oup_req && oup_gnt) begin
                if (oup_data_valid) begin
                    automatic data_t exp_data = exp_queue.get(oup_id);
                    assert (exp_data == oup_data)
                        else $error("Expected to read %0x from ID %0x but got %0x!",
                            exp_data, oup_id, oup_data);
                    if (VERBOSE) begin
                        $display("%0t: read %0x at ID %0x!", $time, oup_data, oup_id);
                    end
                end else begin
                    assert (exp_queue.queues[oup_id].size() == 0)
                        else $error("Expected to get valid output from ID %0x but did not!",
                            oup_id);
                end
            end
        end
    end

    // Model slave at output and consume values.
    initial begin
        void'(std::randomize(oup_id));
        oup_pop = 1'b0;
        wait (rst_n);
        @(posedge clk);
        #(TT);
        forever begin
            @(posedge clk);
            #(TA);
            if (exp_queue.empty()) begin
                oup_pop = 1'b0;
            end else begin
                void'(std::randomize(oup_pop));
                oup_id = exp_queue.rand_id();
            end
            #(TT-TA);
            while (oup_req && !oup_gnt) begin
                @(posedge clk);
                #(TT);
            end
        end
    end

    // Terminate test after specified number of checks is reached.
    initial begin
        static int unsigned n_pops = 0;
        wait (rst_n);
        forever begin
            @(posedge clk);
            #(TT);
            if (oup_req && oup_gnt && oup_pop && oup_data_valid) begin
                n_pops++;
            end
            #(TCLK-TT);
            if (n_pops >= N_CHECKS) begin
                $display("Finished with a total of %0d random entries fed through the ID queue.",
                    n_pops);
                $finish(0);
            end
        end
    end

endmodule
