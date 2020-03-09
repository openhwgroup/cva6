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
// Andreas Kurth  <akurth@iis.ee.ethz.ch>

package axi_pkg;

  typedef logic [1:0] burst_t;
  typedef logic [1:0] resp_t;
  typedef logic [3:0] cache_t;
  typedef logic [2:0] prot_t;
  typedef logic [3:0] qos_t;
  typedef logic [3:0] region_t;
  typedef logic [7:0] len_t;
  typedef logic [2:0] size_t;
  typedef logic [5:0] atop_t; // atomic operations
  typedef logic [3:0] nsaid_t; // non-secure address identifier

  localparam BURST_FIXED = 2'b00;
  localparam BURST_INCR  = 2'b01;
  localparam BURST_WRAP  = 2'b10;

  localparam RESP_OKAY   = 2'b00;
  localparam RESP_EXOKAY = 2'b01;
  localparam RESP_SLVERR = 2'b10;
  localparam RESP_DECERR = 2'b11;

  localparam CACHE_BUFFERABLE = 4'b0001;
  localparam CACHE_MODIFIABLE = 4'b0010;
  localparam CACHE_RD_ALLOC   = 4'b0100;
  localparam CACHE_WR_ALLOC   = 4'b1000;

  // Maximum number of bytes per burst, as specified by `size` (see Table A3-2).
  function automatic shortint unsigned num_bytes(size_t size);
    return 1 << size;
  endfunction

  // An overly long address type lets us define functions that work generically for shorter
  // addresses.  We rely on the synthesizer to optimize the unused bits away.
  typedef logic [127:0] largest_addr_t;

  // Aligned address of burst (see A3-51).
  function automatic largest_addr_t aligned_addr(largest_addr_t addr, size_t size);
    return (addr >> size) << size;
  endfunction

  // Address of beat (see A3-51).
  function automatic largest_addr_t
  beat_addr(largest_addr_t addr, size_t size, shortint unsigned i_beat);
    if (i_beat == 0) begin
      return addr;
    end else begin
      return aligned_addr(addr, size) + i_beat * num_bytes(size);
    end
  endfunction

  // Index of lowest beat in byte (see A3-51).
  function automatic shortint unsigned
  beat_lower_byte(largest_addr_t addr, size_t size, shortint unsigned strobe_width,
      shortint unsigned i_beat);
    largest_addr_t _addr = beat_addr(addr, size, i_beat);
    return _addr - (_addr / strobe_width) * strobe_width;
  endfunction

  // Index of highest beat in byte (see A3-51).
  function automatic shortint unsigned
  beat_upper_byte(largest_addr_t addr, size_t size, shortint unsigned strobe_width,
      shortint unsigned i_beat);
    if (i_beat == 0) begin
      return aligned_addr(addr, size) + (num_bytes(size) - 1) - (addr / strobe_width) * strobe_width;
    end else begin
      return beat_lower_byte(addr, size, strobe_width, i_beat) + num_bytes(size) - 1;
    end
  endfunction

  // MEMORY TYPE
  typedef enum logic [3:0] {
    DEVICE_NONBUFFERABLE,
    DEVICE_BUFFERABLE,
    NORMAL_NONCACHEABLE_NONBUFFERABLE,
    NORMAL_NONCACHEABLE_BUFFERABLE,
    WTHRU_NOALLOCATE,
    WTHRU_RALLOCATE,
    WTHRU_WALLOCATE,
    WTHRU_RWALLOCATE,
    WBACK_NOALLOCATE,
    WBACK_RALLOCATE,
    WBACK_WALLOCATE,
    WBACK_RWALLOCATE
  } mem_type_t;

  function automatic logic [3:0] get_arcache(mem_type_t mtype);
    unique case (mtype)
      DEVICE_NONBUFFERABLE              : return 4'b0000;
      DEVICE_BUFFERABLE                 : return 4'b0001;
      NORMAL_NONCACHEABLE_NONBUFFERABLE : return 4'b0010;
      NORMAL_NONCACHEABLE_BUFFERABLE    : return 4'b0011;
      WTHRU_NOALLOCATE                  : return 4'b1010;
      WTHRU_RALLOCATE                   : return 4'b1110;
      WTHRU_WALLOCATE                   : return 4'b1010;
      WTHRU_RWALLOCATE                  : return 4'b1110;
      WBACK_NOALLOCATE                  : return 4'b1011;
      WBACK_RALLOCATE                   : return 4'b1111;
      WBACK_WALLOCATE                   : return 4'b1011;
      WBACK_RWALLOCATE                  : return 4'b1111;
    endcase // mtype
  endfunction

  function automatic logic [3:0] get_awcache(mem_type_t mtype);
    unique case (mtype)
      DEVICE_NONBUFFERABLE              : return 4'b0000;
      DEVICE_BUFFERABLE                 : return 4'b0001;
      NORMAL_NONCACHEABLE_NONBUFFERABLE : return 4'b0010;
      NORMAL_NONCACHEABLE_BUFFERABLE    : return 4'b0011;
      WTHRU_NOALLOCATE                  : return 4'b0110;
      WTHRU_RALLOCATE                   : return 4'b0110;
      WTHRU_WALLOCATE                   : return 4'b1110;
      WTHRU_RWALLOCATE                  : return 4'b1110;
      WBACK_NOALLOCATE                  : return 4'b0111;
      WBACK_RALLOCATE                   : return 4'b0111;
      WBACK_WALLOCATE                   : return 4'b1111;
      WBACK_RWALLOCATE                  : return 4'b1111;
    endcase // mtype
  endfunction

  // ATOP[5:0]
  localparam ATOP_ATOMICSWAP  = 6'b110000;
  localparam ATOP_ATOMICCMP   = 6'b110001;
  // ATOP[5:4]
  localparam ATOP_NONE        = 2'b00;
  localparam ATOP_ATOMICSTORE = 2'b01;
  localparam ATOP_ATOMICLOAD  = 2'b10;
  // ATOP[3]
  localparam ATOP_LITTLE_END  = 1'b0;
  localparam ATOP_BIG_END     = 1'b1;
  // ATOP[2:0]
  localparam ATOP_ADD   = 3'b000;
  localparam ATOP_CLR   = 3'b001;
  localparam ATOP_EOR   = 3'b010;
  localparam ATOP_SET   = 3'b011;
  localparam ATOP_SMAX  = 3'b100;
  localparam ATOP_SMIN  = 3'b101;
  localparam ATOP_UMAX  = 3'b110;
  localparam ATOP_UMIN  = 3'b111;

  // `xbar_latency_e` and `xbar_cfg_t` are documented in `doc/axi_xbar.md`.
  localparam logic [9:0] DemuxAw = (1 << 9);
  localparam logic [9:0] DemuxW  = (1 << 8);
  localparam logic [9:0] DemuxB  = (1 << 7);
  localparam logic [9:0] DemuxAr = (1 << 6);
  localparam logic [9:0] DemuxR  = (1 << 5);
  localparam logic [9:0] MuxAw   = (1 << 4);
  localparam logic [9:0] MuxW    = (1 << 3);
  localparam logic [9:0] MuxB    = (1 << 2);
  localparam logic [9:0] MuxAr   = (1 << 1);
  localparam logic [9:0] MuxR    = (1 << 0);
  typedef enum logic [9:0] {
    NO_LATENCY    = 10'b000_00_000_00,
    CUT_SLV_AX    = DemuxAw | DemuxAr,
    CUT_MST_AX    = MuxAw | MuxAr,
    CUT_ALL_AX    = DemuxAw | DemuxAr | MuxAw | MuxAr,
    CUT_SLV_PORTS = DemuxAw | DemuxW | DemuxB | DemuxAr | DemuxR,
    CUT_MST_PORTS = MuxAw | MuxW | MuxB | MuxAr | MuxR,
    CUT_ALL_PORTS = 10'b111_11_111_11
  } xbar_latency_e;
  typedef struct packed {
    int unsigned   NoSlvPorts;
    int unsigned   NoMstPorts;
    int unsigned   MaxMstTrans;
    int unsigned   MaxSlvTrans;
    bit            FallThrough;
    xbar_latency_e LatencyMode;
    int unsigned   AxiIdWidthSlvPorts;
    int unsigned   AxiIdUsedSlvPorts;
    int unsigned   AxiAddrWidth;
    int unsigned   AxiDataWidth;
    int unsigned   NoAddrRules;
  } xbar_cfg_t;

  // Commonly used rule types for `axi_xbar`: 64- and 32-bit addresses.
  typedef struct packed {
    int unsigned idx;
    logic [63:0] start_addr;
    logic [63:0] end_addr;
  } xbar_rule_64_t;
  typedef struct packed {
    int unsigned idx;
    logic [31:0] start_addr;
    logic [31:0] end_addr;
  } xbar_rule_32_t;
endpackage
