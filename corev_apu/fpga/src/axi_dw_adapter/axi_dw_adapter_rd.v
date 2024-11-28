/*

Copyright (c) 2018 Alex Forencich

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.

*/

// Language: Verilog 2001

`resetall
`timescale 1ns / 1ps
`default_nettype none

/*
 * AXI4 width adapter
 */
module axi_dw_adapter_rd #
(
    // Width of address bus in bits
    parameter ADDR_WIDTH = 32,
    // Width of input (slave) interface data bus in bits
    parameter S_DATA_WIDTH = 32,
    // Width of input (slave) interface wstrb (width of data bus in words)
    parameter S_STRB_WIDTH = (S_DATA_WIDTH/8),
    // Width of output (master) interface data bus in bits
    parameter M_DATA_WIDTH = 32,
    // Width of output (master) interface wstrb (width of data bus in words)
    parameter M_STRB_WIDTH = (M_DATA_WIDTH/8),
    // Width of ID signal
    parameter ID_WIDTH = 8,
    // Propagate aruser signal
    parameter ARUSER_ENABLE = 0,
    // Width of aruser signal
    parameter ARUSER_WIDTH = 1,
    // Propagate ruser signal
    parameter RUSER_ENABLE = 0,
    // Width of ruser signal
    parameter RUSER_WIDTH = 1,
    // When adapting to a wider bus, re-pack full-width burst instead of passing through narrow burst if possible
    parameter CONVERT_BURST = 1,
    // When adapting to a wider bus, re-pack all bursts instead of passing through narrow burst if possible
    parameter CONVERT_NARROW_BURST = 0,
    // Forward ID through adapter
    parameter FORWARD_ID = 0
)
(
    input  wire                     clk,
    input  wire                     rst,

    /*
     * AXI slave interface
     */
    input  wire [ID_WIDTH-1:0]      s_axi_arid,
    input  wire [ADDR_WIDTH-1:0]    s_axi_araddr,
    input  wire [7:0]               s_axi_arlen,
    input  wire [2:0]               s_axi_arsize,
    input  wire [1:0]               s_axi_arburst,
    input  wire                     s_axi_arlock,
    input  wire [3:0]               s_axi_arcache,
    input  wire [2:0]               s_axi_arprot,
    input  wire [3:0]               s_axi_arqos,
    input  wire [3:0]               s_axi_arregion,
    input  wire [ARUSER_WIDTH-1:0]  s_axi_aruser,
    input  wire                     s_axi_arvalid,
    output wire                     s_axi_arready,
    output wire [ID_WIDTH-1:0]      s_axi_rid,
    output wire [S_DATA_WIDTH-1:0]  s_axi_rdata,
    output wire [1:0]               s_axi_rresp,
    output wire                     s_axi_rlast,
    output wire [RUSER_WIDTH-1:0]   s_axi_ruser,
    output wire                     s_axi_rvalid,
    input  wire                     s_axi_rready,

    /*
     * AXI master interface
     */
    output wire [ID_WIDTH-1:0]      m_axi_arid,
    output wire [ADDR_WIDTH-1:0]    m_axi_araddr,
    output wire [7:0]               m_axi_arlen,
    output wire [2:0]               m_axi_arsize,
    output wire [1:0]               m_axi_arburst,
    output wire                     m_axi_arlock,
    output wire [3:0]               m_axi_arcache,
    output wire [2:0]               m_axi_arprot,
    output wire [3:0]               m_axi_arqos,
    output wire [3:0]               m_axi_arregion,
    output wire [ARUSER_WIDTH-1:0]  m_axi_aruser,
    output wire                     m_axi_arvalid,
    input  wire                     m_axi_arready,
    input  wire [ID_WIDTH-1:0]      m_axi_rid,
    input  wire [M_DATA_WIDTH-1:0]  m_axi_rdata,
    input  wire [1:0]               m_axi_rresp,
    input  wire                     m_axi_rlast,
    input  wire [RUSER_WIDTH-1:0]   m_axi_ruser,
    input  wire                     m_axi_rvalid,
    output wire                     m_axi_rready
);

parameter S_ADDR_BIT_OFFSET = $clog2(S_STRB_WIDTH);
parameter M_ADDR_BIT_OFFSET = $clog2(M_STRB_WIDTH);
parameter S_WORD_WIDTH = S_STRB_WIDTH;
parameter M_WORD_WIDTH = M_STRB_WIDTH;
parameter S_WORD_SIZE = S_DATA_WIDTH/S_WORD_WIDTH;
parameter M_WORD_SIZE = M_DATA_WIDTH/M_WORD_WIDTH;
parameter S_BURST_SIZE = $clog2(S_STRB_WIDTH);
parameter M_BURST_SIZE = $clog2(M_STRB_WIDTH);

// output bus is wider
parameter EXPAND = M_STRB_WIDTH > S_STRB_WIDTH;
parameter DATA_WIDTH = EXPAND ? M_DATA_WIDTH : S_DATA_WIDTH;
parameter STRB_WIDTH = EXPAND ? M_STRB_WIDTH : S_STRB_WIDTH;
// required number of segments in wider bus
parameter SEGMENT_COUNT = EXPAND ? (M_STRB_WIDTH / S_STRB_WIDTH) : (S_STRB_WIDTH / M_STRB_WIDTH);
// data width and keep width per segment
parameter SEGMENT_DATA_WIDTH = DATA_WIDTH / SEGMENT_COUNT;
parameter SEGMENT_STRB_WIDTH = STRB_WIDTH / SEGMENT_COUNT;

// bus width assertions
initial begin
    if (S_WORD_SIZE * S_STRB_WIDTH != S_DATA_WIDTH) begin
        $error("Error: AXI slave interface data width not evenly divisble (instance %m)");
        $finish;
    end

    if (M_WORD_SIZE * M_STRB_WIDTH != M_DATA_WIDTH) begin
        $error("Error: AXI master interface data width not evenly divisble (instance %m)");
        $finish;
    end

    if (S_WORD_SIZE != M_WORD_SIZE) begin
        $error("Error: word size mismatch (instance %m)");
        $finish;
    end

    if (2**$clog2(S_WORD_WIDTH) != S_WORD_WIDTH) begin
        $error("Error: AXI slave interface word width must be even power of two (instance %m)");
        $finish;
    end

    if (2**$clog2(M_WORD_WIDTH) != M_WORD_WIDTH) begin
        $error("Error: AXI master interface word width must be even power of two (instance %m)");
        $finish;
    end
end

localparam [1:0]
    STATE_IDLE = 2'd0,
    STATE_DATA = 2'd1,
    STATE_DATA_READ = 2'd2,
    STATE_DATA_SPLIT = 2'd3;

reg [1:0] state_reg = STATE_IDLE, state_next;

reg [ID_WIDTH-1:0] id_reg = {ID_WIDTH{1'b0}}, id_next;
reg [ADDR_WIDTH-1:0] addr_reg = {ADDR_WIDTH{1'b0}}, addr_next;
reg [DATA_WIDTH-1:0] data_reg = {DATA_WIDTH{1'b0}}, data_next;
reg [1:0] resp_reg = 2'd0, resp_next;
reg [RUSER_WIDTH-1:0] ruser_reg = {RUSER_WIDTH{1'b0}}, ruser_next;
reg [7:0] burst_reg = 8'd0, burst_next;
reg [2:0] burst_size_reg = 3'd0, burst_size_next;
reg [7:0] master_burst_reg = 8'd0, master_burst_next;
reg [2:0] master_burst_size_reg = 3'd0, master_burst_size_next;

reg s_axi_arready_reg = 1'b0, s_axi_arready_next;

reg [ID_WIDTH-1:0] m_axi_arid_reg = {ID_WIDTH{1'b0}}, m_axi_arid_next;
reg [ADDR_WIDTH-1:0] m_axi_araddr_reg = {ADDR_WIDTH{1'b0}}, m_axi_araddr_next;
reg [7:0] m_axi_arlen_reg = 8'd0, m_axi_arlen_next;
reg [2:0] m_axi_arsize_reg = 3'd0, m_axi_arsize_next;
reg [1:0] m_axi_arburst_reg = 2'd0, m_axi_arburst_next;
reg m_axi_arlock_reg = 1'b0, m_axi_arlock_next;
reg [3:0] m_axi_arcache_reg = 4'd0, m_axi_arcache_next;
reg [2:0] m_axi_arprot_reg = 3'd0, m_axi_arprot_next;
reg [3:0] m_axi_arqos_reg = 4'd0, m_axi_arqos_next;
reg [3:0] m_axi_arregion_reg = 4'd0, m_axi_arregion_next;
reg [ARUSER_WIDTH-1:0] m_axi_aruser_reg = {ARUSER_WIDTH{1'b0}}, m_axi_aruser_next;
reg m_axi_arvalid_reg = 1'b0, m_axi_arvalid_next;
reg m_axi_rready_reg = 1'b0, m_axi_rready_next;

// internal datapath
reg  [ID_WIDTH-1:0]     s_axi_rid_int;
reg  [S_DATA_WIDTH-1:0] s_axi_rdata_int;
reg  [1:0]              s_axi_rresp_int;
reg                     s_axi_rlast_int;
reg  [RUSER_WIDTH-1:0]  s_axi_ruser_int;
reg                     s_axi_rvalid_int;
reg                     s_axi_rready_int_reg = 1'b0;
wire                    s_axi_rready_int_early;

assign s_axi_arready = s_axi_arready_reg;

assign m_axi_arid = FORWARD_ID ? m_axi_arid_reg : {ID_WIDTH{1'b0}};
assign m_axi_araddr = m_axi_araddr_reg;
assign m_axi_arlen = m_axi_arlen_reg;
assign m_axi_arsize = m_axi_arsize_reg;
assign m_axi_arburst = m_axi_arburst_reg;
assign m_axi_arlock = m_axi_arlock_reg;
assign m_axi_arcache = m_axi_arcache_reg;
assign m_axi_arprot = m_axi_arprot_reg;
assign m_axi_arqos = m_axi_arqos_reg;
assign m_axi_arregion = m_axi_arregion_reg;
assign m_axi_aruser = ARUSER_ENABLE ? m_axi_aruser_reg : {ARUSER_WIDTH{1'b0}};
assign m_axi_arvalid = m_axi_arvalid_reg;
assign m_axi_rready = m_axi_rready_reg;

always @* begin
    state_next = STATE_IDLE;

    id_next = id_reg;
    addr_next = addr_reg;
    data_next = data_reg;
    resp_next = resp_reg;
    ruser_next = ruser_reg;
    burst_next = burst_reg;
    burst_size_next = burst_size_reg;
    master_burst_next = master_burst_reg;
    master_burst_size_next = master_burst_size_reg;

    s_axi_arready_next = 1'b0;
    m_axi_arid_next = m_axi_arid_reg;
    m_axi_araddr_next = m_axi_araddr_reg;
    m_axi_arlen_next = m_axi_arlen_reg;
    m_axi_arsize_next = m_axi_arsize_reg;
    m_axi_arburst_next = m_axi_arburst_reg;
    m_axi_arlock_next = m_axi_arlock_reg;
    m_axi_arcache_next = m_axi_arcache_reg;
    m_axi_arprot_next = m_axi_arprot_reg;
    m_axi_arqos_next = m_axi_arqos_reg;
    m_axi_arregion_next = m_axi_arregion_reg;
    m_axi_aruser_next = m_axi_aruser_reg;
    m_axi_arvalid_next = m_axi_arvalid_reg && !m_axi_arready;
    m_axi_rready_next = 1'b0;

    if (SEGMENT_COUNT == 1) begin
        // master output is same width; direct transfer with no splitting/merging
        s_axi_rid_int = id_reg;
        s_axi_rdata_int = m_axi_rdata;
        s_axi_rresp_int = m_axi_rresp;
        s_axi_rlast_int = m_axi_rlast;
        s_axi_ruser_int = m_axi_ruser;
        s_axi_rvalid_int = 0;

        case (state_reg)
            STATE_IDLE: begin
                // idle state; wait for new burst
                s_axi_arready_next = !m_axi_arvalid;

                if (s_axi_arready && s_axi_arvalid) begin
                    s_axi_arready_next = 1'b0;
                    id_next = s_axi_arid;
                    m_axi_arid_next = s_axi_arid;
                    m_axi_araddr_next = s_axi_araddr;
                    m_axi_arlen_next = s_axi_arlen;
                    m_axi_arsize_next = s_axi_arsize;
                    m_axi_arburst_next = s_axi_arburst;
                    m_axi_arlock_next = s_axi_arlock;
                    m_axi_arcache_next = s_axi_arcache;
                    m_axi_arprot_next = s_axi_arprot;
                    m_axi_arqos_next = s_axi_arqos;
                    m_axi_arregion_next = s_axi_arregion;
                    m_axi_aruser_next = s_axi_aruser;
                    m_axi_arvalid_next = 1'b1;
                    m_axi_rready_next = s_axi_rready_int_early;
                    state_next = STATE_DATA;
                end else begin
                    state_next = STATE_IDLE;
                end
            end
            STATE_DATA: begin
                // data state; transfer read data
                m_axi_rready_next = s_axi_rready_int_early;

                if (m_axi_rready && m_axi_rvalid) begin
                    s_axi_rid_int = id_reg;
                    s_axi_rdata_int = m_axi_rdata;
                    s_axi_rresp_int = m_axi_rresp;
                    s_axi_rlast_int = m_axi_rlast;
                    s_axi_ruser_int = m_axi_ruser;
                    s_axi_rvalid_int = 1'b1;
                    if (m_axi_rlast) begin
                        // last data word, return to idle
                        m_axi_rready_next = 1'b0;
                        s_axi_arready_next = !m_axi_arvalid;
                        state_next = STATE_IDLE;
                    end else begin
                        state_next = STATE_DATA;
                    end
                end else begin
                    state_next = STATE_DATA;
                end
            end
        endcase
    end else if (EXPAND) begin
        // master output is wider; split reads
        s_axi_rid_int = id_reg;
        s_axi_rdata_int = m_axi_rdata;
        s_axi_rresp_int = m_axi_rresp;
        s_axi_rlast_int = m_axi_rlast;
        s_axi_ruser_int = m_axi_ruser;
        s_axi_rvalid_int = 0;

        case (state_reg)
            STATE_IDLE: begin
                // idle state; wait for new burst
                s_axi_arready_next = !m_axi_arvalid;

                if (s_axi_arready && s_axi_arvalid) begin
                    s_axi_arready_next = 1'b0;
                    id_next = s_axi_arid;
                    m_axi_arid_next = s_axi_arid;
                    m_axi_araddr_next = s_axi_araddr;
                    addr_next = s_axi_araddr;
                    burst_next = s_axi_arlen;
                    burst_size_next = s_axi_arsize;
                    if (CONVERT_BURST && s_axi_arcache[1] && (CONVERT_NARROW_BURST || s_axi_arsize == S_BURST_SIZE)) begin
                        // split reads
                        // require CONVERT_BURST and arcache[1] set
                        master_burst_size_next = M_BURST_SIZE;
                        if (CONVERT_NARROW_BURST) begin
                            m_axi_arlen_next = (({{S_ADDR_BIT_OFFSET+1{1'b0}}, s_axi_arlen} << s_axi_arsize) + s_axi_araddr[M_ADDR_BIT_OFFSET-1:0]) >> M_BURST_SIZE;
                        end else begin
                            m_axi_arlen_next = ({1'b0, s_axi_arlen} + s_axi_araddr[M_ADDR_BIT_OFFSET-1:S_ADDR_BIT_OFFSET]) >> $clog2(SEGMENT_COUNT);
                        end
                        m_axi_arsize_next = M_BURST_SIZE;
                        state_next = STATE_DATA_READ;
                    end else begin
                        // output narrow burst
                        master_burst_size_next = s_axi_arsize;
                        m_axi_arlen_next = s_axi_arlen;
                        m_axi_arsize_next = s_axi_arsize;
                        state_next = STATE_DATA;
                    end
                    m_axi_arburst_next = s_axi_arburst;
                    m_axi_arlock_next = s_axi_arlock;
                    m_axi_arcache_next = s_axi_arcache;
                    m_axi_arprot_next = s_axi_arprot;
                    m_axi_arqos_next = s_axi_arqos;
                    m_axi_arregion_next = s_axi_arregion;
                    m_axi_aruser_next = s_axi_aruser;
                    m_axi_arvalid_next = 1'b1;
                    m_axi_rready_next = s_axi_rready_int_early;
                end else begin
                    state_next = STATE_IDLE;
                end
            end
            STATE_DATA: begin
                m_axi_rready_next = s_axi_rready_int_early;

                if (m_axi_rready && m_axi_rvalid) begin
                    s_axi_rid_int = id_reg;
                    s_axi_rdata_int = m_axi_rdata >> (addr_reg[M_ADDR_BIT_OFFSET-1:S_ADDR_BIT_OFFSET] * S_DATA_WIDTH);
                    s_axi_rresp_int = m_axi_rresp;
                    s_axi_rlast_int = m_axi_rlast;
                    s_axi_ruser_int = m_axi_ruser;
                    s_axi_rvalid_int = 1'b1;
                    addr_next = addr_reg + (1 << burst_size_reg);
                    if (m_axi_rlast) begin
                        m_axi_rready_next = 1'b0;
                        s_axi_arready_next = !m_axi_arvalid;
                        state_next = STATE_IDLE;
                    end else begin
                        state_next = STATE_DATA;
                    end
                end else begin
                    state_next = STATE_DATA;
                end
            end
            STATE_DATA_READ: begin
                m_axi_rready_next = s_axi_rready_int_early;

                if (m_axi_rready && m_axi_rvalid) begin
                    s_axi_rid_int = id_reg;
                    data_next = m_axi_rdata;
                    resp_next = m_axi_rresp;
                    ruser_next = m_axi_ruser;
                    s_axi_rdata_int = m_axi_rdata >> (addr_reg[M_ADDR_BIT_OFFSET-1:S_ADDR_BIT_OFFSET] * S_DATA_WIDTH);
                    s_axi_rresp_int = m_axi_rresp;
                    s_axi_rlast_int = 1'b0;
                    s_axi_ruser_int = m_axi_ruser;
                    s_axi_rvalid_int = 1'b1;
                    burst_next = burst_reg - 1;
                    addr_next = addr_reg + (1 << burst_size_reg);
                    if (burst_reg == 0) begin
                        m_axi_rready_next = 1'b0;
                        s_axi_arready_next = !m_axi_arvalid;
                        s_axi_rlast_int = 1'b1;
                        state_next = STATE_IDLE;
                    end else if (addr_next[master_burst_size_reg] != addr_reg[master_burst_size_reg]) begin
                        state_next = STATE_DATA_READ;
                    end else begin
                        m_axi_rready_next = 1'b0;
                        state_next = STATE_DATA_SPLIT;
                    end
                end else begin
                    state_next = STATE_DATA_READ;
                end
            end
            STATE_DATA_SPLIT: begin
                m_axi_rready_next = 1'b0;

                if (s_axi_rready_int_reg) begin
                    s_axi_rid_int = id_reg;
                    s_axi_rdata_int = data_reg >> (addr_reg[M_ADDR_BIT_OFFSET-1:S_ADDR_BIT_OFFSET] * S_DATA_WIDTH);
                    s_axi_rresp_int = resp_reg;
                    s_axi_rlast_int = 1'b0;
                    s_axi_ruser_int = ruser_reg;
                    s_axi_rvalid_int = 1'b1;
                    burst_next = burst_reg - 1;
                    addr_next = addr_reg + (1 << burst_size_reg);
                    if (burst_reg == 0) begin
                        s_axi_arready_next = !m_axi_arvalid;
                        s_axi_rlast_int = 1'b1;
                        state_next = STATE_IDLE;
                    end else if (addr_next[master_burst_size_reg] != addr_reg[master_burst_size_reg]) begin
                        m_axi_rready_next = s_axi_rready_int_early;
                        state_next = STATE_DATA_READ;
                    end else begin
                        state_next = STATE_DATA_SPLIT;
                    end
                end else begin
                    state_next = STATE_DATA_SPLIT;
                end
            end
        endcase
    end else begin
        // master output is narrower; merge reads and possibly split burst
        s_axi_rid_int = id_reg;
        s_axi_rdata_int = data_reg;
        s_axi_rresp_int = resp_reg;
        s_axi_rlast_int = 1'b0;
        s_axi_ruser_int = m_axi_ruser;
        s_axi_rvalid_int = 0;

        case (state_reg)
            STATE_IDLE: begin
                // idle state; wait for new burst
                s_axi_arready_next = !m_axi_arvalid;

                resp_next = 2'd0;

                if (s_axi_arready && s_axi_arvalid) begin
                    s_axi_arready_next = 1'b0;
                    id_next = s_axi_arid;
                    m_axi_arid_next = s_axi_arid;
                    m_axi_araddr_next = s_axi_araddr;
                    addr_next = s_axi_araddr;
                    burst_next = s_axi_arlen;
                    burst_size_next = s_axi_arsize;
                    if (s_axi_arsize > M_BURST_SIZE) begin
                        // need to adjust burst size
                        if (s_axi_arlen >> (8+M_BURST_SIZE-s_axi_arsize) != 0) begin
                            // limit burst length to max
                            master_burst_next = (8'd255 << (s_axi_arsize-M_BURST_SIZE)) | ((~s_axi_araddr & (8'hff >> (8-s_axi_arsize))) >> M_BURST_SIZE);
                        end else begin
                            master_burst_next = (s_axi_arlen << (s_axi_arsize-M_BURST_SIZE)) | ((~s_axi_araddr & (8'hff >> (8-s_axi_arsize))) >> M_BURST_SIZE);
                        end
                        master_burst_size_next = M_BURST_SIZE;
                        m_axi_arlen_next = master_burst_next;
                        m_axi_arsize_next = master_burst_size_next;
                    end else begin
                        // pass through narrow (enough) burst
                        master_burst_next = s_axi_arlen;
                        master_burst_size_next = s_axi_arsize;
                        m_axi_arlen_next = s_axi_arlen;
                        m_axi_arsize_next = s_axi_arsize;
                    end
                    m_axi_arburst_next = s_axi_arburst;
                    m_axi_arlock_next = s_axi_arlock;
                    m_axi_arcache_next = s_axi_arcache;
                    m_axi_arprot_next = s_axi_arprot;
                    m_axi_arqos_next = s_axi_arqos;
                    m_axi_arregion_next = s_axi_arregion;
                    m_axi_aruser_next = s_axi_aruser;
                    m_axi_arvalid_next = 1'b1;
                    m_axi_rready_next = 1'b0;
                    state_next = STATE_DATA;
                end else begin
                    state_next = STATE_IDLE;
                end
            end
            STATE_DATA: begin
                m_axi_rready_next = s_axi_rready_int_early && !m_axi_arvalid;

                if (m_axi_rready && m_axi_rvalid) begin
                    data_next[addr_reg[S_ADDR_BIT_OFFSET-1:M_ADDR_BIT_OFFSET]*SEGMENT_DATA_WIDTH +: SEGMENT_DATA_WIDTH] = m_axi_rdata;
                    if (m_axi_rresp) begin
                        resp_next = m_axi_rresp;
                    end
                    s_axi_rid_int = id_reg;
                    s_axi_rdata_int = data_next;
                    s_axi_rresp_int = resp_next;
                    s_axi_rlast_int = 1'b0;
                    s_axi_ruser_int = m_axi_ruser;
                    s_axi_rvalid_int = 1'b0;
                    master_burst_next = master_burst_reg - 1;
                    addr_next = (addr_reg + (1 << master_burst_size_reg)) & ({ADDR_WIDTH{1'b1}} << master_burst_size_reg);
                    m_axi_araddr_next = addr_next;
                    if (addr_next[burst_size_reg] != addr_reg[burst_size_reg]) begin
                        data_next = {DATA_WIDTH{1'b0}};
                        burst_next = burst_reg - 1;
                        s_axi_rvalid_int = 1'b1;
                    end
                    if (master_burst_reg == 0) begin
                        if (burst_next >> (8+M_BURST_SIZE-burst_size_reg) != 0) begin
                            // limit burst length to max
                            master_burst_next = 8'd255;
                        end else begin
                            master_burst_next = (burst_next << (burst_size_reg-M_BURST_SIZE)) | (8'hff >> (8-burst_size_reg) >> M_BURST_SIZE);
                        end
                        m_axi_arlen_next = master_burst_next;

                        if (burst_reg == 0) begin
                            m_axi_rready_next = 1'b0;
                            s_axi_rlast_int = 1'b1;
                            s_axi_rvalid_int = 1'b1;
                            s_axi_arready_next = !m_axi_arvalid;
                            state_next = STATE_IDLE;
                        end else begin
                            // start new burst
                            m_axi_arvalid_next = 1'b1;
                            m_axi_rready_next = 1'b0;
                            state_next = STATE_DATA;
                        end
                    end else begin
                        state_next = STATE_DATA;
                    end
                end else begin
                    state_next = STATE_DATA;
                end
            end
        endcase
    end
end

always @(posedge clk) begin
    state_reg <= state_next;

    id_reg <= id_next;
    addr_reg <= addr_next;
    data_reg <= data_next;
    resp_reg <= resp_next;
    ruser_reg <= ruser_next;
    burst_reg <= burst_next;
    burst_size_reg <= burst_size_next;
    master_burst_reg <= master_burst_next;
    master_burst_size_reg <= master_burst_size_next;

    s_axi_arready_reg <= s_axi_arready_next;

    m_axi_arid_reg <= m_axi_arid_next;
    m_axi_araddr_reg <= m_axi_araddr_next;
    m_axi_arlen_reg <= m_axi_arlen_next;
    m_axi_arsize_reg <= m_axi_arsize_next;
    m_axi_arburst_reg <= m_axi_arburst_next;
    m_axi_arlock_reg <= m_axi_arlock_next;
    m_axi_arcache_reg <= m_axi_arcache_next;
    m_axi_arprot_reg <= m_axi_arprot_next;
    m_axi_arqos_reg <= m_axi_arqos_next;
    m_axi_arregion_reg <= m_axi_arregion_next;
    m_axi_aruser_reg <= m_axi_aruser_next;
    m_axi_arvalid_reg <= m_axi_arvalid_next;
    m_axi_rready_reg <= m_axi_rready_next;

    if (rst) begin
        state_reg <= STATE_IDLE;

        s_axi_arready_reg <= 1'b0;

        m_axi_arvalid_reg <= 1'b0;
        m_axi_rready_reg <= 1'b0;
    end
end

// output datapath logic
reg [ID_WIDTH-1:0]     s_axi_rid_reg    = {ID_WIDTH{1'b0}};
reg [S_DATA_WIDTH-1:0] s_axi_rdata_reg  = {S_DATA_WIDTH{1'b0}};
reg [1:0]              s_axi_rresp_reg  = 2'd0;
reg                    s_axi_rlast_reg  = 1'b0;
reg [RUSER_WIDTH-1:0]  s_axi_ruser_reg  = 1'b0;
reg                    s_axi_rvalid_reg = 1'b0, s_axi_rvalid_next;

reg [ID_WIDTH-1:0]     temp_s_axi_rid_reg    = {ID_WIDTH{1'b0}};
reg [S_DATA_WIDTH-1:0] temp_s_axi_rdata_reg  = {S_DATA_WIDTH{1'b0}};
reg [1:0]              temp_s_axi_rresp_reg  = 2'd0;
reg                    temp_s_axi_rlast_reg  = 1'b0;
reg [RUSER_WIDTH-1:0]  temp_s_axi_ruser_reg  = 1'b0;
reg                    temp_s_axi_rvalid_reg = 1'b0, temp_s_axi_rvalid_next;

// datapath control
reg store_axi_r_int_to_output;
reg store_axi_r_int_to_temp;
reg store_axi_r_temp_to_output;

assign s_axi_rid    = s_axi_rid_reg;
assign s_axi_rdata  = s_axi_rdata_reg;
assign s_axi_rresp  = s_axi_rresp_reg;
assign s_axi_rlast  = s_axi_rlast_reg;
assign s_axi_ruser  = RUSER_ENABLE ? s_axi_ruser_reg : {RUSER_WIDTH{1'b0}};
assign s_axi_rvalid = s_axi_rvalid_reg;

// enable ready input next cycle if output is ready or the temp reg will not be filled on the next cycle (output reg empty or no input)
assign s_axi_rready_int_early = s_axi_rready | (~temp_s_axi_rvalid_reg & (~s_axi_rvalid_reg | ~s_axi_rvalid_int));

always @* begin
    // transfer sink ready state to source
    s_axi_rvalid_next = s_axi_rvalid_reg;
    temp_s_axi_rvalid_next = temp_s_axi_rvalid_reg;

    store_axi_r_int_to_output = 1'b0;
    store_axi_r_int_to_temp = 1'b0;
    store_axi_r_temp_to_output = 1'b0;

    if (s_axi_rready_int_reg) begin
        // input is ready
        if (s_axi_rready | ~s_axi_rvalid_reg) begin
            // output is ready or currently not valid, transfer data to output
            s_axi_rvalid_next = s_axi_rvalid_int;
            store_axi_r_int_to_output = 1'b1;
        end else begin
            // output is not ready, store input in temp
            temp_s_axi_rvalid_next = s_axi_rvalid_int;
            store_axi_r_int_to_temp = 1'b1;
        end
    end else if (s_axi_rready) begin
        // input is not ready, but output is ready
        s_axi_rvalid_next = temp_s_axi_rvalid_reg;
        temp_s_axi_rvalid_next = 1'b0;
        store_axi_r_temp_to_output = 1'b1;
    end
end

always @(posedge clk) begin
    if (rst) begin
        s_axi_rvalid_reg <= 1'b0;
        s_axi_rready_int_reg <= 1'b0;
        temp_s_axi_rvalid_reg <= 1'b0;
    end else begin
        s_axi_rvalid_reg <= s_axi_rvalid_next;
        s_axi_rready_int_reg <= s_axi_rready_int_early;
        temp_s_axi_rvalid_reg <= temp_s_axi_rvalid_next;
    end

    // datapath
    if (store_axi_r_int_to_output) begin
        s_axi_rid_reg <= s_axi_rid_int;
        s_axi_rdata_reg <= s_axi_rdata_int;
        s_axi_rresp_reg <= s_axi_rresp_int;
        s_axi_rlast_reg <= s_axi_rlast_int;
        s_axi_ruser_reg <= s_axi_ruser_int;
    end else if (store_axi_r_temp_to_output) begin
        s_axi_rid_reg <= temp_s_axi_rid_reg;
        s_axi_rdata_reg <= temp_s_axi_rdata_reg;
        s_axi_rresp_reg <= temp_s_axi_rresp_reg;
        s_axi_rlast_reg <= temp_s_axi_rlast_reg;
        s_axi_ruser_reg <= temp_s_axi_ruser_reg;
    end

    if (store_axi_r_int_to_temp) begin
        temp_s_axi_rid_reg <= s_axi_rid_int;
        temp_s_axi_rdata_reg <= s_axi_rdata_int;
        temp_s_axi_rresp_reg <= s_axi_rresp_int;
        temp_s_axi_rlast_reg <= s_axi_rlast_int;
        temp_s_axi_ruser_reg <= s_axi_ruser_int;
    end
end

endmodule

`resetall
