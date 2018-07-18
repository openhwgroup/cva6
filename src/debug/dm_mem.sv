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
    parameter int NrHarts     = -1
)(
    input  logic                             clk_i,       // Clock
    input  logic                             dmactive_i,  // debug module reset

    output logic                             debug_req_o,
    input  logic [19:0]                      hartsel_i,
    // from Ctrl and Status register
    input  logic [NrHarts-1:0]               haltreq_i,
    input  logic [NrHarts-1:0]               resumereq_i,

    // state bits
    output logic [NrHarts-1:0]               halted_o,    // hart acknowledge halt
    output logic [NrHarts-1:0]               resuming_o,  // hart is resuming

    input  logic [dm::ProgBufSize-1:0][31:0] progbuf_i,    // program buffer to expose

    input  logic [dm::DataCount-1:0][31:0]   data_i,       // data in
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

    localparam int HartSelLen = (NrHarts == 1) ? 1 : $clog2(NrHarts);
    localparam DbgAddressBits  = 12;
    localparam logic [DbgAddressBits-1:0] DataBase = (dm::DataAddr);
    localparam logic [DbgAddressBits-1:0] DataEnd = (dm::DataAddr + 4*dm::DataCount);
    localparam logic [DbgAddressBits-1:0] ProgBufBase = (dm::DataAddr - 4*dm::ProgBufSize);
    localparam logic [DbgAddressBits-1:0] ProgBufEnd = (dm::DataAddr - 1);
    localparam logic [DbgAddressBits-1:0] AbstractCmdBase = (ProgBufBase - 4*2);
    localparam logic [DbgAddressBits-1:0] AbstractCmdEnd = (ProgBufBase - 1);
    localparam logic [DbgAddressBits-1:0] WhereTo = 'h300;
    localparam logic [DbgAddressBits-1:0] FlagsBase   = 'h400;
    localparam logic [DbgAddressBits-1:0] FlagsEnd     = 'h7FF;


    localparam logic [DbgAddressBits-1:0] Halted    = 'h100;
    localparam logic [DbgAddressBits-1:0] Going     = 'h104;
    localparam logic [DbgAddressBits-1:0] Resuming  = 'h108;
    localparam logic [DbgAddressBits-1:0] Exception = 'h10C;
    // localparam logic [7:0] FlagGo     = 7'b0;
    // localparam logic [7:0] FlagResume = 7'b1;

    logic [NrHarts-1:0] halted_d, halted_q;
    logic [NrHarts-1:0] resuming_d, resuming_q;
    logic               resume, go, going;

    logic [HartSelLen-1:0] hart_sel;
    logic exception, halted;
    logic unsupported_command;

    logic [63:0] rom_rdata;
    logic [63:0] rdata_d, rdata_q;
    // distinguish whether we need to forward data from the ROM or the FSM
    // latch the address for this
    logic fwd_rom_d, fwd_rom_q;
    dm::ac_ar_cmd_t ac_ar;

    // Abstract Command Access Register
    assign ac_ar       = dm::ac_ar_cmd_t'(cmd_i.control);
    assign hart_sel    = wdata_i[HartSelLen-1:0];
    assign debug_req_o = haltreq_i;
    assign halted_o    = halted_q;
    assign resuming_o  = resuming_q;

    enum logic [1:0] { Idle, Go, Resume, CmdExecuting } state_d, state_q;

    // hart ctrl queue
    always_comb begin
        cmderror_valid_o = 1'b0;
        cmderror_o       = dm::CmdErrNone;
        state_d          = state_q;
        go               = 1'b0;
        resume           = 1'b0;
        cmdbusy_o        = 1'b1;

        case (state_q)
            Idle: begin
                cmdbusy_o = 1'b0;
                if (cmd_valid_i && halted_q) begin
                    // give the go signal
                    state_d = Go;
                end else if (cmd_valid_i) begin
                    // hart must be halted for all requests
                    cmderror_valid_o = 1'b1;
                    cmderror_o = dm::CmdErrorHaltResume;
                end
                // CSRs want to resume, the request is ignored when the hart is
                // requested to halt
                if (resumereq_i && !haltreq_i && halted_q) begin
                    state_d = Resume;
                end
            end

            Go: begin
                // we are already busy here since we scheduled the execution of a program
                cmdbusy_o = 1'b1;
                go        = 1'b1;
                // the thread is now executing the command, track its state
                if (going)
                    state_d = CmdExecuting;
            end

            Resume: begin
                cmdbusy_o = 1'b1;
                resume = 1'b1;
                if (resuming_o)
                    state_d = Idle;
            end

            CmdExecuting: begin
                cmdbusy_o = 1'b1;
                go        = 1'b0;
                // wait until the hart has halted again
                if (halted) begin
                    state_d = Idle;
                end
            end
        endcase

        if (exception) begin
            cmderror_valid_o = 1'b1;
            cmderror_o = dm::CmdErrorException;
        end

        if (unsupported_command) begin
            cmderror_valid_o = 1'b1;
            cmderror_o = dm::CmdErrNotSupported;
        end
    end

    // read/write logic
    always_comb begin
        automatic logic [63:0] data_bits;

        halted_d     = halted_q;
        resuming_d   = resuming_q;
        rdata_o      = fwd_rom_q ? rom_rdata : rdata_q;
        rdata_d      = rdata_q;
        // convert the data in bits representation
        data_bits    = data_i;
        // write data in csr register
        data_valid_o = 1'b0;
        exception    = 1'b0;
        halted       = 1'b0;
        going        = 1'b0;
        // this abstract command is currently unsupported
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
                    Going: going = 1'b1;
                    Resuming: begin
                        halted_d[hart_sel] = 1'b0;
                        resuming_d[hart_sel] = 1'b1;
                    end
                    // an exception occurred during execution
                    Exception: exception = 1'b1;
                    // core can write data registers
                    // TODO(zarubaf) Remove hard-coded values
                    [(dm::DataAddr):DataEnd]: begin

                        data_valid_o = 1'b1;
                        for (int i = 0; i < $bits(be_i); i++) begin
                            if (be_i[i]) begin
                                data_bits[i*8+:8] = wdata_i[i*8+:8];
                            end
                        end
                    end
                endcase

            // this is a read
            end else begin
                unique case (addr_i[DbgAddressBits-1:0]) inside
                    // variable ROM content
                    WhereTo: begin
                        // variable jump to abstract cmd, program_buffer or resume
                        if (resumereq_i) begin
                            rdata_d = {32'b0, riscv::jalr(0, 0, dm::ResumeAddress)};
                        end

                        // there is a command active so jump there
                        if (cmdbusy_o) begin
                            rdata_d = {32'b0, riscv::jalr(0, 0, AbstractCmdBase)};
                        end
                    end

                    // TODO(zarubaf) change hard-coded values
                    [DataBase:DataEnd]: begin
                        rdata_d = {data_i[1], data_i[0]};
                    end

                    // TODO(zarubaf) change hard-coded values
                    [ProgBufBase:ProgBufEnd]: begin
                        case (addr_i)
                            ProgBufBase + 16: rdata_d = {progbuf_i[5], progbuf_i[4]};
                            ProgBufBase + 8:  rdata_d = {progbuf_i[3], progbuf_i[2]};
                            ProgBufBase:      rdata_d = {progbuf_i[1], progbuf_i[0]};
                        endcase
                    end

                    // two slots for abstract command
                    [AbstractCmdBase:AbstractCmdEnd]: begin
                        // $display("Reading from abstract command @%x", addr_i);
                        rdata_d = '0;
                        // this depends on the command being executed
                        unique case (cmd_i.cmdtype)
                            // --------------------
                            // Access Register
                            // --------------------
                            dm::AccessRegister: begin
                                if (ac_ar.aarsize >= 4) begin
                                    // illegal size in that case issue a sq instruction which will throw an illegal instruction
                                    rdata_d[31:0] = riscv::store(ac_ar.aarsize, ac_ar.regno[4:0], 0, dm::DataAddr);
                                end else if (ac_ar.transfer && ac_ar.write) begin
                                    rdata_d[31:0] = riscv::load(ac_ar.aarsize, ac_ar.regno[4:0], 0, dm::DataAddr);
                                end else if (ac_ar.transfer && !ac_ar.write) begin
                                    rdata_d[31:0] = riscv::store(ac_ar.aarsize, ac_ar.regno[4:0], 0, dm::DataAddr);
                                end
                                // check whether we need to execute the program buffer
                                if (ac_ar.postexec) begin
                                    // issue a nop, we will automatically run into the program buffer
                                    rdata_d[63:32] = riscv::nop();
                                end else begin
                                    // transfer control back to idle loop
                                    rdata_d[63:32] = riscv::ebreak();
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
                    // harts are polling for flags here
                    [FlagsBase:FlagsEnd]: begin
                        // release the corresponding hart
                        if (({addr_i[DbgAddressBits-1:3], 3'b0} - FlagsBase) == {hartsel_i[19:3], 3'b0}) begin
                            rdata_d[hartsel_i[2:0]+:8] = {6'b0, resume, go};
                        end
                    end
                    default: ;
                endcase
            end
        end

        data_o = data_bits;
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
            state_q    <= Idle;
        end else begin
            fwd_rom_q  <= fwd_rom_d;
            rdata_q    <= rdata_d;
            halted_q   <= halted_d;
            resuming_q <= resuming_d;
            state_q    <= state_d;
        end
    end

endmodule
