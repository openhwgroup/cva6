/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_mem.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   11.7.2018
 *
 * Description: Memory module for execution-based debug clients
 *
 */

module dm_mem #(
    parameter int NrHarts = -1
)(
    input  logic                             clk_i,       // Clock
    input  logic                             dmactive_i,  // debug module reset

    output logic                             debug_req_o,
    // from Ctrl and Status register
    input  logic [NrHarts-1:0]               haltreq_i,
    input  logic [NrHarts-1:0]               resumereq_i,

    // state bits
    output logic [NrHarts-1:0]               halted_o,    // hart acknowledge halt
    output logic [NrHarts-1:0]               resuming_o,  // hart is resuming

    input  logic [dm::ProgBufSize-1:0][31:0] progbuf_i,    // program buffer to expose

    output logic [dm::DataCount-1:0][31:0]   data_i,       // data in
    output logic [dm::DataCount-1:0][31:0]   data_o,       // data out
    output logic                             data_valid_o, // data out is valid
    // abstract command interface
    input  logic                             cmd_valid_i,
    input  dm::command_t                     cmd_i,
    output logic                             cmderror_valid_o,
    output dm::cmderr_t                      cmderror_o,
    output logic                             cmdbusy_o,
    // data interface

    // SRAM interface
    input  logic                             req_i,
    input  logic                             we_i,
    input  logic [63:0]                      addr_i,
    input  logic [63:0]                      wdata_i,
    input  logic [7:0]                       be_i,
    output logic [63:0]                      rdata_o
);

    localparam DbgAddressBits  = 12;
    localparam HartSelLen      = (NrHarts == 1) ? 1 : $clog2(NrHarts);
    localparam DataAddr        = dm::DataAddr;
    localparam ProgBufBase     = dm::DataAddr - 4*dm::DataCount;
    localparam AbstractCmdBase = ProgBufBase - 4*dm::ProgBufSize;

    localparam logic [DbgAddressBits-1:0] Halted    = 'h100;
    localparam logic [DbgAddressBits-1:0] Going     = 'h104;
    localparam logic [DbgAddressBits-1:0] Resuming  = 'h108;
    localparam logic [DbgAddressBits-1:0] Exception = 'h10C;
    localparam logic [DbgAddressBits-1:0] WhereTo   = 'h300;
    localparam logic [DbgAddressBits-1:0] Flags     = 'h400;
    localparam logic [7:0] FlagGo     = 7'b0;
    localparam logic [7:0] FlagResume = 7'b1;

    logic [NrHarts-1:0] halted_d, halted_q;
    logic [NrHarts-1:0] resuming_d, resuming_q;
    logic               cmdbusy_d, cmdbusy_q;

    logic [HartSelLen-1:0] hart_sel;
    logic going, exception, halted;
    logic unsupported_command;

    logic [63:0] rom_rdata;
    logic [63:0] rdata_d, rdata_q;
    // distinguish whether we need to forward data from the ROM or the FSM
    // latch the address for this
    logic fwd_rom_d, fwd_rom_q;

    assign hart_sel    = wdata_i[HartSelLen-1:0];
    assign debug_req_o = haltreq_i;
    assign halted_o    = halted_q;
    assign resuming_o  = resuming_q;
    assign cmdbusy_o   = cmdbusy_q;

    // abstract command ctrl
    always_comb begin
        cmderror_valid_o = 1'b0;
        cmderror_o       = '0;
        cmdbusy_d        = cmdbusy_q;

        if (exception) begin
            cmderror_valid_o = 1'b1;
            cmderror_o = dm::CmdErrorException;
        end

        // we've got a new command
        if (cmd_valid_i && halted_q) begin
            cmdbusy_d = 1'b1;
            // release the go flag
        end else if (cmd_valid_i) begin
            // hart must be halted for all requests
            cmderror_valid_o = 1'b1;
            cmderror_o = dm::CmdErrorHaltResume;
        end

        // we've halted again ~> clear the busy flag
        if (halted) begin
            cmdbusy_d = 1'b0;
        end

        if (unsupported_command) begin
            cmderror_valid_o = 1'b1;
            cmderror_o = dm::CmdErrNotSupported;
        end
    end

    // read/write logic
    always_comb begin
        halted_d     = halted_q;
        resuming_d   = resuming_q;
        rdata_o      = fwd_rom_q ? rom_rdata : rdata_q;
        rdata_d      = rdata_q;
        data_o       = data_i;
        // write data in csr register
        data_valid_o = 1'b0;
        exception    = 1'b0;
        halted       = 1'b0;
        unsupported_command = 1'b0;
        // we've got a new request
        if (req_i) begin
            // this is a write
            if (we_i) begin
                unique case (addr_i[DbgAddressBits-1:0]) inside
                    Halted: begin
                        halted = 1'b1;
                        halted_d[hart_sel] = 1'b1;
                        resuming_d[hart_sel] = 1'b0;
                    end
                    Going:;
                    Resuming: begin
                        halted_d[hart_sel] = 1'b0;
                        resuming_d[hart_sel] = 1'b1;
                    end
                    // an exception occurred during execution
                    Exception: exception = 1'b1;
                    // core can write data registers
                    // TODO(zarubaf) Remove hard-coded values
                    (dm::DataAddr || dm::DataAddr+4): begin
                        // data_valid_o = 1'b1;
                        for (int i = 0; i < $bits(be_i); i++) begin
                            if (be_i[i]) begin
                                // data_o = wdata_i[i*8+:8];
                            end
                        end
                    end

                    // harts are polling for flags here
                    [Flags:AbstractCmdBase] begin

                    end
                endcase

            // this is a read
            end else begin
                unique case (addr_i[DbgAddressBits-1:0]) inside
                    // variable ROM content
                    WhereTo: begin
                        // variable jump to abstract cmd, program_buffer or resume
                        if (resumereq_i) begin
                            rdata_d = {32'b0, riscv::jal(0, dm::ResumeAddress)};
                        end

                        // there is a command active so jump there
                        if (cmdbusy_q) begin
                            rdata_d = {32'b0, riscv::jal(0, AbstractCmdBase)};
                        end
                    end

                    // TODO(zarubaf) change hard-coded values
                    // TODO(zarubaf) submit verilator bug report
                    // %Error: Internal Error: src/debug/dm_mem.sv:129: ../V3Hashed.cpp:73: sameHash function undefined (returns 0) for node under CFunc.
                    (dm::DataAddr || dm::DataAddr+4): begin
                        rdata_d = {data_i[1], data_i[0]};
                    end

                    [ProgBufBase:(dm::DataAddr-4)]: begin
                        // TODO(zarubaf) change hard-coded values
                        rdata_d = {progbuf_i[1], progbuf_i[0]};
                    end
                    // two slots for abstract command
                    [AbstractCmdBase:AbstractCmdBase+4]: begin
                        rdata_d = '0;
                        // this depends on the command being executed
                        unique case (cmd_i.cmdtype)
                            // --------------------
                            // Access Register
                            // --------------------
                            dm::AccessRegister: begin
                                automatic dm::ac_ar_cmd_t ac_ar;
                                ac_ar = dm::ac_ar_cmd_t'(cmd_i.control);

                                if (ac_ar.transfer && ac_ar.write) begin
                                    rdata_d[0] = riscv::store(ac_ar.aarsize, ac_ar.regno[4:0], 0, dm::DataAddr);
                                end else if (ac_ar.transfer) begin
                                    rdata_d[0] = riscv::load(ac_ar.aarsize, ac_ar.regno[4:0], 0, dm::DataAddr);
                                end
                                // check whether we need to execute the program buffer
                                if (ac_ar.postexec) begin
                                    // issue a nop, we will automatically run into the program buffer
                                    rdata_d[1] = riscv::nop();
                                end else begin
                                    // transfer control back to idle loop
                                    rdata_d[1] = riscv::ebreak();
                                end
                            end
                            // not supported at the moment
                            // dm::QuickAccess:;
                            // dm::AccessMemory:;
                            default: begin
                                unsupported_command = 1'b1;
                            end
                        endcase
                    end
                endcase
            end
        end
    end

    debug_rom i_debug_rom (
        .clk_i,
        .req_i,
        .addr_i,
        .rdata_o (rom_rdata)
    );

    // ROM starts at the HaltAddress of the core e.g.: it immediately jumps to
    // the ROM base address
    assign fwd_rom_d = (addr_i[DbgAddressBits-1:0] >= dm::HaltAddress) ? 1'b1 : 1'b0;

    always_ff @(posedge clk_i) begin
        if (~dmactive_i) begin
            fwd_rom_q  <= 1'b0;
            rdata_q    <= '0;
            halted_q   <= 1'b0;
            resuming_q <= 1'b0;
            cmdbusy_q  <= 1'b0;
        end else begin
            fwd_rom_q  <= fwd_rom_d;
            rdata_q    <= rdata_d;
            halted_q   <= halted_d;
            resuming_q <= resuming_d;
            cmdbusy_q  <= cmdbusy_d;
        end
    end

endmodule
