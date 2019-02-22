// ========== Copyright Header Begin ============================================
// Copyright (c) 2015 Princeton University
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of Princeton University nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY PRINCETON UNIVERSITY "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL PRINCETON UNIVERSITY BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// ========== Copyright Header End ============================================

//==================================================================================================
//  Filename      : piton_sd_define.vh
//  Created On    : 2017-03-15
//  Last Modified : 2018-11-21 22:12:24
//  Revision      :
//  Author        : Ang Li
//  Company       : Princeton University
//  Email         : angl@princeton.edu
//
//  Description   :
//==================================================================================================

// ------ Configurable Parameters ------ //
`define CACHE_ENTRY_WIDTH       3   // Need to re-configure BRAM in the SD cache if set larger than 3
`define CACHE_INDEX_WIDTH       1   // Must be smaller than CACHE_ENTRY_WIDTH

// ------ DO NOT TOUCH ------ //
`define PHY_ADDR_BITS           `PHY_ADDR_WIDTH-1:0

`define SD_ADDR_WIDTH           32
`define SD_BLOCK_OFFSET_WIDTH   9

`define PHY_BLOCK_BITS          `PHY_ADDR_WIDTH-1:`SD_BLOCK_OFFSET_WIDTH


`define CACHE_ENTRY_BITS        (`SD_BLOCK_OFFSET_WIDTH+`CACHE_ENTRY_WIDTH-1):`SD_BLOCK_OFFSET_WIDTH

`define CACHE_ENTRIES           (2 ** `CACHE_ENTRY_WIDTH)

`define CACHE_INDEXES           (2 ** `CACHE_INDEX_WIDTH)
`define CACHE_ENTRY_INDEXED_WIDTH   (`CACHE_ENTRY_WIDTH-`CACHE_INDEX_WIDTH)
`define CACHE_ENTRY_INDEXED_BITS    (`SD_BLOCK_OFFSET_WIDTH+`CACHE_ENTRY_WIDTH-1):(`SD_BLOCK_OFFSET_WIDTH+`CACHE_INDEX_WIDTH)
`define CACHE_ENTRIES_INDEXED   (2 ** `CACHE_ENTRY_INDEXED_WIDTH)
`define CACHE_INDEX_BITS        (`SD_BLOCK_OFFSET_WIDTH+`CACHE_INDEX_WIDTH-1):`SD_BLOCK_OFFSET_WIDTH
`define CACHE_BLOCK_PLACEMENT_BITS  `PHY_ADDR_WIDTH-1:(`SD_BLOCK_OFFSET_WIDTH+`CACHE_INDEX_WIDTH)

`define ADDR_LINE_BITS          (`CACHE_ENTRY_WIDTH+`SD_BLOCK_OFFSET_WIDTH-1):3

`define NOC_DATA_BITS           64-1:0

// Tile config
// /scratch2/michscha/projects/serpent-pulp/piton/design/./xilinx/genesys2/devices_ariane.xml
`define NUM_TILES 1
`define X_TILES 1
`define Y_TILES 1
// NoC interface
`define NOC_DATA_WIDTH      64
`define NOC_CHIPID_WIDTH    `CHIP_ID_WIDTH
`define NOC_CHIPID_OFFCHIP  13
`define NOC_CHIPID_ONCHIP   12:0
`define NOC_X_WIDTH         `XY_WIDTH
`define NOC_Y_WIDTH         `XY_WIDTH
`define NOC_OFF_CHIP_NODE_X `OFF_CHIP_NODE_X
`define NOC_OFF_CHIP_NODE_Y `OFF_CHIP_NODE_Y
`define NOC_FBITS_WIDTH     `FINAL_BITS
`define NOC_FBITS_RESERVED  4'd1
`define NOC_FBITS_L1        4'd0
`define NOC_FBITS_L2        4'd0
`define NOC_FBITS_FP        4'd0
`define NOC_FBITS_MEM       4'd2
`define NOC_NODEID_WIDTH    34
`define NOC_DATACOUNT_WIDTH 5
`define NOC_EC_WIDTH        5
// NodeID decomposition
`define NOC_NODEID_ONCHIPID     32:20
`define NOC_NODEID_OFFCHIPID    33
`define NOC_NODEID_CHIPID       33:20
`define NOC_NODEID_X            19:12
`define NOC_NODEID_Y            11:4
`define NOC_NODEID_FBITS        3:0
//========================
//Packet format
//=========================
//Header decomposition
`define MSG_HEADER_WIDTH        192
`define MSG_LAST_SUBLINE        0
`define MSG_SUBLINE_ID          2:1
`define MSG_L2_MISS             3
`define MSG_MESI                5:4
`define MSG_OPTIONS_1           5:0
`define MSG_OPTIONS_4           5:0
`define MSG_MSHRID              13:6
`define MSG_TYPE                21:14
`define MSG_TYPE_LO             14
`define MSG_LENGTH              29:22
`define MSG_LENGTH_LO           22
`define MSG_DST_FBITS           33:30
`define MSG_DST_Y               41:34
`define MSG_DST_X               49:42
`define MSG_DST_CHIPID          63:50
`define MSG_DST_CHIPID_HI       63
`define MSG_DATA_SIZE           74:72
`define MSG_CACHE_TYPE          75
`define MSG_SUBLINE_VECTOR      79:76
`define MSG_ADDR                119:80
`define MSG_LSID                147:142
`define MSG_SDID                157:148
`define MSG_SRC_FBITS           161:158
`define MSG_SRC_Y               169:162
`define MSG_SRC_X               177:170
`define MSG_SRC_CHIPID          191:178
// these shifted fields are added for convienience
// HEADER 2
`define MSG_DATA_SIZE_           10:8
`define MSG_CACHE_TYPE_          11
`define MSG_SUBLINE_VECTOR_      15:12
`define MSG_OPTIONS_2_           15:0
`define MSG_ADDR_HI_             55
`define MSG_ADDR_                55:16
// HEADER 3
`define MSG_LSID_                19:14 // 147-128:142-128
`define MSG_SDID_                29:20
`define MSG_OPTIONS_3_           29:0
`define MSG_SRC_FBITS_           33:30
`define MSG_SRC_Y_               41:34
`define MSG_SRC_X_               49:42
`define MSG_SRC_CHIPID_          63:50
//NoC header information
`define MSG_FLIT_WIDTH          `NOC_DATA_WIDTH
`define MSG_DST_CHIPID_WIDTH    `NOC_CHIPID_WIDTH
`define MSG_DST_X_WIDTH         `NOC_X_WIDTH
`define MSG_DST_Y_WIDTH         `NOC_Y_WIDTH
`define MSG_DST_FBITS_WIDTH     `NOC_FBITS_WIDTH
`define MSG_DST_NODEID_WIDTH    `NOC_NODEID_WIDTH
`define MSG_LENGTH_WIDTH        8
`define MSG_OPTIONS_1_WIDTH     6
// Width of MSG_ADDR field - you're probably looking for PHY_ADDR_WIDTH
`define MSG_ADDR_WIDTH          48
//Coherence information
`define MSG_TYPE_WIDTH          8
//Requests from L15 to L2
// Should always make #0 an error
`define MSG_TYPE_RESERVED           8'd0
`define MSG_TYPE_LOAD_REQ           8'd31
`define MSG_TYPE_PREFETCH_REQ       8'd1
`define MSG_TYPE_STORE_REQ          8'd2
`define MSG_TYPE_BLK_STORE_REQ      8'd3
`define MSG_TYPE_BLKINIT_STORE_REQ  8'd4
`define MSG_TYPE_CAS_REQ            8'd5
`define MSG_TYPE_CAS_P1_REQ         8'd6
//condition satisfied
`define MSG_TYPE_CAS_P2Y_REQ        8'd7
//condition not satisfied
`define MSG_TYPE_CAS_P2N_REQ        8'd8
//Both SWAP and LDSTUB are the same for L2
`define MSG_TYPE_SWAP_REQ           8'd9
`define MSG_TYPE_SWAP_P1_REQ        8'd10
`define MSG_TYPE_SWAP_P2_REQ        8'd11
`define MSG_TYPE_WB_REQ             8'd12
`define MSG_TYPE_WBGUARD_REQ        8'd13
`define MSG_TYPE_NC_LOAD_REQ        8'd14
`define MSG_TYPE_NC_STORE_REQ       8'd15
`define MSG_TYPE_INTERRUPT_FWD       8'd32
//RISC-V AMO requests
`define MSG_TYPE_AMO_ADD_REQ         8'd36
`define MSG_TYPE_AMO_AND_REQ         8'd37
`define MSG_TYPE_AMO_OR_REQ          8'd38
`define MSG_TYPE_AMO_XOR_REQ         8'd39
`define MSG_TYPE_AMO_MAX_REQ         8'd40
`define MSG_TYPE_AMO_MAXU_REQ        8'd41
`define MSG_TYPE_AMO_MIN_REQ         8'd42
`define MSG_TYPE_AMO_MINU_REQ        8'd43
//RISC-V AMO L2-internal phase 1
`define MSG_TYPE_AMO_ADD_P1_REQ      8'd44
`define MSG_TYPE_AMO_AND_P1_REQ      8'd45
`define MSG_TYPE_AMO_OR_P1_REQ       8'd46
`define MSG_TYPE_AMO_XOR_P1_REQ      8'd47
`define MSG_TYPE_AMO_MAX_P1_REQ      8'd48
`define MSG_TYPE_AMO_MAXU_P1_REQ     8'd49
`define MSG_TYPE_AMO_MIN_P1_REQ      8'd50
`define MSG_TYPE_AMO_MINU_P1_REQ     8'd51
//RISC-V AMO L2-internal phase 2
`define MSG_TYPE_AMO_ADD_P2_REQ      8'd52
`define MSG_TYPE_AMO_AND_P2_REQ      8'd53
`define MSG_TYPE_AMO_OR_P2_REQ       8'd54
`define MSG_TYPE_AMO_XOR_P2_REQ      8'd55
`define MSG_TYPE_AMO_MAX_P2_REQ      8'd56
`define MSG_TYPE_AMO_MAXU_P2_REQ     8'd57
`define MSG_TYPE_AMO_MIN_P2_REQ      8'd58
`define MSG_TYPE_AMO_MINU_P2_REQ     8'd59
`define MSG_TYPE_LR_REQ              8'd60
//Forward requests from L2 to L15
`define MSG_TYPE_LOAD_FWD           8'd16
`define MSG_TYPE_STORE_FWD          8'd17
`define MSG_TYPE_INV_FWD            8'd18
//Memory requests from L2 to DRAM
`define MSG_TYPE_LOAD_MEM           8'd19
`define MSG_TYPE_STORE_MEM          8'd20
//Forward acks from L15 to L2
`define MSG_TYPE_LOAD_FWDACK        8'd21
`define MSG_TYPE_STORE_FWDACK       8'd22
`define MSG_TYPE_INV_FWDACK         8'd23
//Memory acks from memory to L2
`define MSG_TYPE_LOAD_MEM_ACK       8'd24
`define MSG_TYPE_STORE_MEM_ACK      8'd25
`define MSG_TYPE_NC_LOAD_MEM_ACK    8'd26
`define MSG_TYPE_NC_STORE_MEM_ACK   8'd27
//Acks from L2 to L15
`define MSG_TYPE_NODATA_ACK         8'd28
`define MSG_TYPE_DATA_ACK           8'd29
//TODO
`define MSG_TYPE_ERROR              8'd30
`define MSG_TYPE_INTERRUPT          8'd33
//Only exist within L2
`define MSG_TYPE_L2_LINE_FLUSH_REQ   8'd34
`define MSG_TYPE_L2_DIS_FLUSH_REQ    8'd35
//`define MSG_TYPE_LOAD_REQ           8'd31 if this is enabled, don't use 31
`define MSG_CACHE_TYPE_WIDTH        1
`define MSG_CACHE_TYPE_DATA         1'b0
`define MSG_CACHE_TYPE_INS          1'b1
// These should be defined in l2.vh, not the global defines
`define MSG_MESI_BITS               2
`define MSG_MESI_I                  2'b00
`define MSG_MESI_S                  2'b01
`define MSG_MESI_E                  2'b10
`define MSG_MESI_M                  2'b11
`define MSG_SUBLINE_VECTOR_WIDTH    4
`define MSG_SUBLINE_ID_WIDTH        2
`define MSG_LAST_SUBLINE_WIDTH      1
//Physical address
`define PHY_ADDR_WIDTH          40
`define MSG_SRC_CHIPID_WIDTH    `NOC_CHIPID_WIDTH
`define MSG_SRC_X_WIDTH         `NOC_X_WIDTH
`define MSG_SRC_Y_WIDTH         `NOC_Y_WIDTH
`define MSG_SRC_FBITS_WIDTH     `NOC_FBITS_WIDTH
`define MSG_SRC_NODEID_WIDTH    `NOC_NODEID_WIDTH
`define MSG_MSHRID_WIDTH        8
`define MSG_L2_MISS_BITS        1
//Transition data size
`define MSG_DATA_SIZE_WIDTH     3
`define MSG_DATA_SIZE_0B        3'b000
`define MSG_DATA_SIZE_1B        3'b001
`define MSG_DATA_SIZE_2B        3'b010
`define MSG_DATA_SIZE_4B        3'b011
`define MSG_DATA_SIZE_8B        3'b100
`define MSG_DATA_SIZE_16B       3'b101
`define MSG_DATA_SIZE_32B       3'b110
`define MSG_DATA_SIZE_64B       3'b111

//`define DMBR_TAG_WIDTH 4
//Clumpy Shared Memory
`define ASI_IMMU_CSM_IN_REG             8'h0E
`define ASI_DMMU_CSM_IN_REG             8'h0F
`define ASI_IMMU_CSM_ACCESS_REG         8'h12
`define ASI_DMMU_CSM_ACCESS_REG         8'h13
////////////////////////////////////////////
// SOME CONFIGURATION REGISTERS DEFINES
////////////////////////////////////////////
// example: read/write to csm_en would be 0xba_0000_0100
// `define ASI_ADDRESS_MASK    `L15_ADDR_TYPE
// `define CONFIG_ASI_ADDRESS  `L15_ADDR_TYPE_WIDTH'hba
`define CONFIG_REG_ADDRESS_MASK                     15:8 // trin: important mask
`define CONFIG_REG_CHIPID_ADDRESS                   8'd0
`define CONFIG_REG_CSM_EN_ADDRESS                   8'd1
`define CONFIG_REG_DMBR_REG1_ADDRESS                8'd2
`define CONFIG_REG_HMT_BASE_REG                     8'd3
`define CONFIG_SYSTEM_TILE_COUNT_ADDRESS            8'd4
`define CONFIG_REG_DMBR_REG2_ADDRESS                8'd5
`define CONFIG_REG_HOME_ALLOC_METHOD                8'd6
// DMBR Config register 1 fields
`define CFG_DMBR_FUNC_EN_BIT                        8'h0
`define CFG_DMBR_STALL_EN_BIT                       8'h1
`define CFG_DMBR_PROC_LD_BIT                        8'h2
`define CFG_DMBR_RD_CUR_VAL_BIT                     8'h3
`define CFG_DMBR_CRED_BIN_0_BITS                     9:4
`define CFG_DMBR_CRED_BIN_1_BITS                    15:10
`define CFG_DMBR_CRED_BIN_2_BITS                    21:16
`define CFG_DMBR_CRED_BIN_3_BITS                    27:22
`define CFG_DMBR_CRED_BIN_4_BITS                    33:28
`define CFG_DMBR_CRED_BIN_5_BITS                    39:34
`define CFG_DMBR_CRED_BIN_6_BITS                    45:40
`define CFG_DMBR_CRED_BIN_7_BITS                    51:46
`define CFG_DMBR_CRED_BIN_8_BITS                    57:52
`define CFG_DMBR_CRED_BIN_9_BITS                    63:58
// DMBR Config register 2 fields
`define CFG_DMBR_REPLENISH_BITS                     15:0
`define CFG_DMBR_BIN_SCALE_BITS                     25:16
//Home allocation method
`define HOME_ALLOC_METHOD_WIDTH                     2
`define HOME_ALLOC_LOW_ORDER_BITS                   2'd0
`define HOME_ALLOC_MIDDLE_ORDER_BITS                2'd1
`define HOME_ALLOC_HIGH_ORDER_BITS                  2'd2
`define HOME_ALLOC_MIXED_ORDER_BITS                 2'd3
//Additional fields for Sharer Domain ID and Logical Sharer ID
//For coherence domain restriction only
`define MSG_SDID_WIDTH          10
`define MSG_LSID_WIDTH          6
`define MSG_HDID_WIDTH          10
`define MSG_LHID_WIDTH          6
`define TLB_CSM_WIDTH           33
`define TLB_CSM                 32:0
`define TLB_CSM_STATE           32  //0 for local csm info, 1 for global info
`define TLB_CSM_STATE_LOCAL     1'b0
`define TLB_CSM_STATE_GLOBAL    1'b1
`define TLB_CSM_LOCAL           31:0
`define TLB_CSM_HDID            31:22
`define TLB_CSM_HD_SIZE         21:16
`define TLB_CSM_SDID            15:6
`define TLB_CSM_LSID            5:0
`define TLB_CSM_GLOBAL          29:0
`define TLB_CSM_CHIPID          29:16
`define TLB_CSM_Y               15:8
`define TLB_CSM_X               7:0
`define TTE_CSM_WIDTH           64
`define TTE_CSM                 63:0
`define TTE_CSM_HDID            31:22
`define TTE_CSM_HD_SIZE         21:16
`define TTE_CSM_SDID            15:6
`define TTE_CSM_LSID            5:0
//`define TTE_CSM_WIDTH           64
//`define TTE_CSM                 63:0
//`define TTE_CSM_VALID           63
//`define TTE_CSM_SZL             62:61
//`define TTE_CSM_NFO             60
//`define TTE_CSM_IE              59
//`define TTE_CSM_SOFT2           58:49
//`define TTE_CSM_SZH             48
//`define TTE_CSM_DIAG            47:40
//`define TTE_CSM_RES1            39
//`define TTE_CSM_SDID            38:29
//`define TTE_CSM_HDID            28:19
//`define TTE_CSM_LSID            18:13
//`define TTE_CSM_SOFT            12:8
//`define TTE_CSM_RES2            7
//`define TTE_CSM_LOCK            6
//`define TTE_CSM_CP              5
//`define TTE_CSM_CV              4
//`define TTE_CSM_E               3
//`define TTE_CSM_P               2
//`define TTE_CSM_W               1
//`define TTE_CSM_RES3            0
`define HOME_ID_WIDTH               `MSG_LHID_WIDTH
`define HOME_ID_ADDR_POS_LOW        `HOME_ID_WIDTH+5 : 6
`define HOME_ID_ADDR_POS_MIDDLE     `HOME_ID_WIDTH+13 : 14
`define HOME_ID_ADDR_POS_HIGH       `HOME_ID_WIDTH+23 : 24
`define HOME_ID_X_POS_WIDTH         3
`define HOME_ID_X_POS               2:0
`define HOME_ID_Y_POS_WIDTH         3
`define HOME_ID_Y_POS               5:3
// Packet format for home id
`define PACKET_HOME_ID_WIDTH        (`NOC_CHIPID_WIDTH+`NOC_X_WIDTH+`NOC_Y_WIDTH)
`define PACKET_HOME_ID_CHIP_MASK    (`PACKET_HOME_ID_WIDTH-1):(`NOC_X_WIDTH+`NOC_Y_WIDTH)
`define PACKET_HOME_ID_Y_MASK       `NOC_Y_WIDTH+`NOC_X_WIDTH-1:`NOC_X_WIDTH
`define PACKET_HOME_ID_X_MASK       `NOC_X_WIDTH-1:0

