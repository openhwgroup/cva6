// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


//-----------------------------------------
// AXI Master Agent
//
// Converts AXI master transactions into
// Merlin network packets.
//-----------------------------------------
`timescale 1 ns / 1 ns
 
module cva6_intel_altera_merlin_axi_master_ni_1980_4qd7sla
#( 
    //----------------
    // AXI Interface Parameters
    //----------------
   parameter  ID_WIDTH = 2,
              ADDR_WIDTH = 32,
              RDATA_WIDTH = 32,
              WDATA_WIDTH = 32,
              ADDR_USER_WIDTH = 8,
              SAI_WIDTH = 4,
              ADDRCHK_WIDTH = 4,
              DATA_USER_WIDTH = 8,
              USER_DATA_WIDTH = 1,
              AXI_LOCK_WIDTH = 2,
              AXI_BURST_LENGTH_WIDTH = 4,
              WRITE_ISSUING_CAPABILITY = 16,
              READ_ISSUING_CAPABILITY = 16,
              AXI_VERSION = "AXI3",
              ACE_LITE_SUPPORT = 0,
              SYNC_RESET       = 0,                           
    //-------------------------
    // Packet Format Parameters
    //-------------------------
            PKT_THREAD_ID_H = 109,
            PKT_THREAD_ID_L = 108,
            PKT_QOS_H = 113,
            PKT_QOS_L = 110,
            PKT_BEGIN_BURST = 104,
            PKT_CACHE_H = 103,
            PKT_CACHE_L = 100,
            PKT_ADDR_SIDEBAND_H = 99,
            PKT_ADDR_SIDEBAND_L = 92,
            PKT_DATA_SIDEBAND_H = 124,
  
            PKT_DATA_SIDEBAND_L = 118,
            PKT_PROTECTION_H = 89,
            PKT_PROTECTION_L = 87,
            PKT_BURST_SIZE_H = 84, 
            PKT_BURST_SIZE_L = 82,
            PKT_BURST_TYPE_H = 86,
            PKT_BURST_TYPE_L = 85, 
            PKT_RESPONSE_STATUS_L = 106,
            PKT_RESPONSE_STATUS_H = 107,
            PKT_BURSTWRAP_H = 79,
            PKT_BURSTWRAP_L = 77,
            PKT_BYTE_CNT_H = 76,
            PKT_BYTE_CNT_L = 74,
            PKT_ADDR_H = 73,
            PKT_ADDR_L = 42,
            PKT_TRANS_EXCLUSIVE = 80,
            PKT_TRANS_LOCK = 105,
            PKT_TRANS_COMPRESSED_READ = 41,
            PKT_TRANS_POSTED = 40,
            PKT_TRANS_WRITE = 39,
            PKT_TRANS_READ = 38,
            PKT_DATA_H = 37,
            PKT_DATA_L = 6,
            PKT_BYTEEN_H = 5,
            PKT_BYTEEN_L = 2,
            PKT_SRC_ID_H = 1,
            PKT_SRC_ID_L = 1,
            PKT_DEST_ID_H = 0,
            PKT_DEST_ID_L = 0,
            PKT_ORI_BURST_SIZE_H = 127,
            PKT_ORI_BURST_SIZE_L = 125,
            PKT_DOMAIN_L = 128,
            PKT_DOMAIN_H = 129, 
            PKT_SNOOP_L = 130, 
            PKT_SNOOP_H = 133,  
            PKT_BARRIER_L = 134, 
            PKT_BARRIER_H = 135,
            PKT_WUNIQUE = 136,
            PKT_EOP_OOO =137,
            PKT_SOP_OOO =138, 
            PKT_POISON_L  = 138,
            PKT_POISON_H  = 138,
            PKT_DATACHK_L = 139,
            PKT_DATACHK_H = 139,
            PKT_ADDRCHK_L = 140,
            PKT_ADDRCHK_H = 140,
            PKT_SAI_H     = 141,
            PKT_SAI_L     = 141,
            PKT_USER_DATA_L = 142,
            PKT_USER_DATA_H = 142,
            ST_DATA_W     = 143,
            ST_CHANNEL_W  = 1,
            ROLE_BASED_USER = 0,
    //----------------
    // Agent Parameters
    //----------------
            ID = 1,
            USE_PKT_DATACHK       = 1,   
            USE_PKT_ADDRCHK       = 1,   
    //----------------
    // Derived Parameters
    //----------------
            PKT_BURSTWRAP_W = PKT_BURSTWRAP_H - PKT_BURSTWRAP_L + 1,
            PKT_BYTE_CNT_W = PKT_BYTE_CNT_H - PKT_BYTE_CNT_L + 1,
            PKT_ADDR_W = PKT_ADDR_H - PKT_ADDR_L + 1,
            PKT_DATA_W = PKT_DATA_H - PKT_DATA_L + 1,
            PKT_BYTEEN_W = PKT_BYTEEN_H - PKT_BYTEEN_L + 1,
            PKT_SRC_ID_W = PKT_SRC_ID_H - PKT_SRC_ID_L + 1,
            PKT_DEST_ID_W = PKT_DEST_ID_H - PKT_DEST_ID_L + 1,
            PKT_DATACHK_W     = (USE_PKT_DATACHK)? PKT_DATACHK_H - PKT_DATACHK_L + 1: 1,  // field width in packet shrinks to 1 when inactive (should be done by transform already)
            DATACHK_WIDTH     = WDATA_WIDTH / 8,
            POISON_WIDTH      = (WDATA_WIDTH + 64 -1) / 64 , // ceil(WDATA_WIDTH/64) workaround 
            PADDING_ZERO      = (ADDRCHK_WIDTH*8) - ADDR_WIDTH,
            PARITY_ADDR_WIDTH =  PADDING_ZERO + ADDR_WIDTH,
            SKIP_USER_ADDRCHK_CAL        =  (ADDRCHK_WIDTH*8 < ADDR_WIDTH)
            
)
(
    //----------------
    // Global Signals
    //----------------
    input                                aclk,
    input                                aresetn,
    //----------------------------
    // AXI SLAVE SIDE INTERFACES
    //----------------------------
    // Write Address Channel
    //----------------
    input [ID_WIDTH-1:0]                 awid,
    input [ADDR_WIDTH-1:0]               awaddr,
    input [AXI_BURST_LENGTH_WIDTH - 1:0] awlen, 
    input [2:0]                          awsize,
    input [1:0]                          awburst,
    input [AXI_LOCK_WIDTH-1:0]           awlock,
    input [3:0]                          awcache,
    input [2:0]                          awprot,
    input [3:0]                          awqos,
    input [3:0]                          awregion, 
    input [ADDR_USER_WIDTH-1:0]          awuser,
    input                                awvalid,
    output                               awready,
    //----------------
    // Write Data Channel
    //----------------
    input [ID_WIDTH-1:0]                 wid,
    input [PKT_DATA_W-1:0]               wdata,
    input [(PKT_DATA_W/8)-1:0]           wstrb,
    input                                wlast,
    input                                wvalid,
    input [DATA_USER_WIDTH-1:0]          wuser,
    output                               wready,
    //----------------
    // Write Response Channel
    //----------------
    output reg [ID_WIDTH-1:0]            bid,
    output reg [1:0]                     bresp,
    output                               bvalid,
    input                                bready,
    output reg [DATA_USER_WIDTH-1:0]     buser, 
    //----------------
    // Read Address Channel
    //----------------
    input [ID_WIDTH-1:0]                 arid,
    input [ADDR_WIDTH-1:0]               araddr,
    input [AXI_BURST_LENGTH_WIDTH - 1:0] arlen,
    input [2:0]                          arsize,
    input [1:0]                          arburst,
    input [AXI_LOCK_WIDTH-1:0]           arlock,
    input [3:0]                          arcache,
    input [2:0]                          arprot,
    input [3:0]                          arqos,
    input [3:0]                          arregion,
    input [ADDR_USER_WIDTH-1:0]          aruser,
    input                                arvalid,
    output                               arready,
 
    //----------------
    // ACE-Lite Specific Signals
    //----------------
    input [1:0]                          ardomain, 
    input [3:0]                          arsnoop,  
    input [1:0]                          arbar,   
 
    input [1:0]                          awdomain, 
    input [2:0]                          awsnoop,  
    input [1:0]                          awbar,    
    input                                awunique,
 
    //----------------
    // Read Data Channel
    //----------------
    output reg [ID_WIDTH-1:0]            rid,
    output reg [PKT_DATA_W-1:0]          rdata,
    output reg [1:0]                     rresp,
    output                               rlast,
    output                               rvalid,
    input                                rready,
    output reg [DATA_USER_WIDTH-1:0]     ruser,
    
    //AXI role base used signals
    input [ADDRCHK_WIDTH-1:0]            awuser_addrchk,
    input [ADDRCHK_WIDTH-1:0]            aruser_addrchk,
    input [SAI_WIDTH-1:0]                awuser_sai,
    input [SAI_WIDTH-1:0]                aruser_sai,
    input [DATACHK_WIDTH-1:0]            wuser_datachk,
    input [USER_DATA_WIDTH-1:0]          wuser_data,
    input [POISON_WIDTH-1:0]             wuser_poison,
    output reg [DATACHK_WIDTH-1:0]            ruser_datachk,
    output reg [POISON_WIDTH-1:0]             ruser_poison,
    output reg [USER_DATA_WIDTH-1:0]          ruser_data,
    //----------------------------
    // NETWORK SIDE INTERFACES
    //----------------------------
    // WRITE Channel 
    //------------------
    // Command Source
    //----------------
    output reg                           write_cp_valid,
    output reg [ST_DATA_W-1:0]           write_cp_data,
    output wire                          write_cp_startofpacket,
    output wire                          write_cp_endofpacket,
    input                                write_cp_ready,
    //----------------
    // Response Sink
    //----------------
    input                                write_rp_valid,
    input [ST_DATA_W-1 : 0]              write_rp_data,
    input [ST_CHANNEL_W-1 : 0]           write_rp_channel,
    input                                write_rp_startofpacket,
    input                                write_rp_endofpacket,
    output reg                           write_rp_ready, 
    //-------------------
    // READ Channel 
    //-------------------
    // Command Source
    //----------------
    output reg                           read_cp_valid,
    output reg [ST_DATA_W-1:0]           read_cp_data,
    output wire                          read_cp_startofpacket,
    output wire                          read_cp_endofpacket,
    input                                read_cp_ready,
    //----------------
    // Response Sink
    //----------------
    input                                read_rp_valid,
    input [ST_DATA_W-1 : 0]              read_rp_data,
    input [ST_CHANNEL_W-1 : 0]           read_rp_channel,
    input                                read_rp_startofpacket,
    input                                read_rp_endofpacket,
    output reg                           read_rp_ready
        
);
 
//--------------------------------------
// Local parameters
//--------------------------------------
localparam NUMSYMBOLS           = PKT_DATA_W/8;
localparam BITS_PER_SYMBOL      = 8;
 
typedef enum bit [1:0] 
{
    FIXED       = 2'b00,
    INCR        = 2'b01,
    WRAP        = 2'b10,
    RESERVED    = 2'b11
} AxiBurstType;
 
//----------------------------------------------------
// AXSIZE decoding
//
// Turns the axsize value into the actual number of bytes
// being transferred.
// ---------------------------------------------------
function reg[7:0] bytes_in_transfer;
    input [2:0] axsize;
 
    case (axsize)
        3'b000: bytes_in_transfer = 8'b00000001;
        3'b001: bytes_in_transfer = 8'b00000010;
        3'b010: bytes_in_transfer = 8'b00000100;
        3'b011: bytes_in_transfer = 8'b00001000;
        3'b100: bytes_in_transfer = 8'b00010000;
        3'b101: bytes_in_transfer = 8'b00100000;
        3'b110: bytes_in_transfer = 8'b01000000;
        3'b111: bytes_in_transfer = 8'b10000000;
        default:bytes_in_transfer = 8'b00000001;
    endcase
 
endfunction
 
    // --------------------------------------------------
 
    // Ceil(log2()) function log2ceil of 4 = 2
 
    // --------------------------------------------------
 
    function integer log2ceil;
 
        input reg[62:0] val;
        reg [63:0] i;
        begin
            i = 1;
            log2ceil = 0;
            while (i < val) begin
                log2ceil = log2ceil + 1;
                i = i << 1;
            end
        end
    endfunction
 
// --------------------------------------------------
// calcParity: calculates byte-level parity signal 
// --------------------------------------------------
function reg [PKT_DATACHK_W-1:0] calcParity (
    input [WDATA_WIDTH-1:0] data
 );
    for (int i=0; i<PKT_DATACHK_W; i++)
        calcParity[i] = ~(^ data[i*8 +:8]);
endfunction
 
//--------------------------------------
//  Burst type decode
//--------------------------------------
AxiBurstType write_burst_type, read_burst_type;
 
function AxiBurstType burst_type_decode 
(
    input [1:0] axburst
);
    AxiBurstType burst_type;
    begin
        case (axburst)
            2'b00    : burst_type = FIXED;
            2'b01    : burst_type = INCR;
            2'b10    : burst_type = WRAP;
            2'b11    : burst_type = RESERVED;
            default  : burst_type = INCR;
        endcase
        return burst_type;
    end
endfunction
 
// Generation of internal reset synchronization
   reg internal_sclr;
 
   generate if (SYNC_RESET == 1) begin : rst_syncronizer
      always @ (posedge aclk) begin
         internal_sclr <= ~aresetn;
      end
   end
   endgenerate
 
 
// register signals: skid buffer
reg [ID_WIDTH-1:0]                      awid_q0;  
reg [ADDR_WIDTH-1:0]                  awaddr_q0;
reg [AXI_BURST_LENGTH_WIDTH - 1:0]     awlen_q0;
reg [2:0]                             awsize_q0;
reg [1:0]                            awburst_q0;
reg [AXI_LOCK_WIDTH-1:0]              awlock_q0;
reg [3:0]                            awcache_q0;
reg [2:0]                             awprot_q0;
reg [3:0]                              awqos_q0;
reg [3:0]                           awregion_q0;
reg [ADDR_USER_WIDTH-1:0]             awuser_q0;
reg                                  awvalid_q0;
reg [1:0]                           awdomain_q0; 
reg [2:0]                            awsnoop_q0;  
reg [1:0]                              awbar_q0;   
reg                                 awunique_q0;
reg [ADDRCHK_WIDTH-1:0]       awuser_addrchk_q0;
reg [SAI_WIDTH-1:0]               awuser_sai_q0;
 
reg [ID_WIDTH-1:0]                       wid_q0; 
reg [PKT_DATA_W-1:0]                   wdata_q0;
reg [(PKT_DATA_W/8)-1:0]               wstrb_q0;
reg                                    wlast_q0;
reg [DATA_USER_WIDTH-1:0]              wuser_q0;
reg                                   wvalid_q0;
reg [DATACHK_WIDTH-1:0]        wuser_datachk_q0;
reg [POISON_WIDTH-1:0]          wuser_poison_q0;
reg [USER_DATA_WIDTH-1:0]         wuser_data_q0;
 
reg [ID_WIDTH-1:0]                      arid_q0;
reg [ADDR_WIDTH-1:0]                  araddr_q0;
reg [AXI_BURST_LENGTH_WIDTH - 1:0]     arlen_q0;
reg [2:0]                             arsize_q0;
reg [1:0]                            arburst_q0;
reg [AXI_LOCK_WIDTH-1:0]              arlock_q0;
reg [3:0]                            arcache_q0;
reg [2:0]                             arprot_q0;
reg [3:0]                              arqos_q0;
reg [3:0]                           arregion_q0;
reg [ADDR_USER_WIDTH-1:0]             aruser_q0;
reg                                  arvalid_q0;
reg [1:0]                           ardomain_q0; 
reg [3:0]                            arsnoop_q0;
reg [1:0]                              arbar_q0;
reg [ADDRCHK_WIDTH-1:0]       aruser_addrchk_q0;
reg [SAI_WIDTH-1:0]               aruser_sai_q0;   

wire                          ar_parity_status;
wire                          aw_parity_status;

wire network_ready;
 
generate 
   if(SYNC_RESET == 0) begin // async_reset
 
      always @ (posedge aclk, negedge aresetn) begin
         if(~aresetn) begin
            awvalid_q0 <= 1'b0;
         end
         else if(~awvalid_q0 || (wvalid_q0 & wlast_q0 & network_ready)) begin
            awvalid_q0 <= awvalid;
         end
      end
 
      always @ (posedge aclk, negedge aresetn) begin
         if(~aresetn) begin
            wvalid_q0 <= 1'b0;
         end
         else if((network_ready && awvalid_q0) || ~wvalid_q0) begin
            wvalid_q0 <= wvalid;
         end
      end
 
      always @ (posedge aclk, negedge aresetn) begin
         if(~aresetn) begin
            arvalid_q0 <= 1'b0;
         end
         else if(read_cp_ready || ~arvalid_q0) begin
            arvalid_q0 <= arvalid;
         end
      end
 
   end   // end async_reset
   else begin  // sync_reset
 
      always @ (posedge aclk) begin
         if(internal_sclr) begin
            awvalid_q0 <= 1'b0;
         end
         else if(~awvalid_q0 || (wvalid_q0 & wlast_q0 & network_ready)) begin
            awvalid_q0 <= awvalid;
         end
      end
 
      always @ (posedge aclk) begin
         if(internal_sclr) begin
            wvalid_q0 <= 1'b0;
         end
         else if((network_ready && awvalid_q0) || ~wvalid_q0) begin
            wvalid_q0 <= wvalid;
         end
      end
 
      always @ (posedge aclk) begin
         if(internal_sclr) begin
            arvalid_q0 <= 1'b0;
         end
         else if(read_cp_ready || ~arvalid_q0) begin
            arvalid_q0 <= arvalid;
         end
      end
 
   end   // end sync_reset
endgenerate
 
// write address channel
always @ (posedge aclk) begin
   if(~awvalid_q0 || (wvalid_q0 & wlast_q0 & network_ready)) begin 
      awid_q0       <=        awid;
      awaddr_q0     <=      awaddr;
      awlen_q0      <=       awlen; 
      awsize_q0     <=      awsize;
      awburst_q0    <=     awburst;
      awlock_q0     <=      awlock;
      awcache_q0    <=     awcache;
      awprot_q0     <=      awprot;
      awqos_q0      <=       awqos;
      awregion_q0   <=    awregion; 
      awuser_q0     <=      awuser;
      awdomain_q0   <=    awdomain;
      awsnoop_q0    <=     awsnoop;
      awbar_q0      <=       awbar;
      awunique_q0   <=    awunique;
      if (ROLE_BASED_USER) begin
         awuser_addrchk_q0 <=   awuser_addrchk;
         awuser_sai_q0     <=   awuser_sai;
      end else begin
         awuser_addrchk_q0 <=  '0; 
         awuser_sai_q0     <=  '0;
      end
   end
end 
 
// write data channel
always @ (posedge aclk) begin
   if((network_ready && awvalid_q0) || ~wvalid_q0) begin
      wid_q0    <=      wid;     
      wdata_q0  <=    wdata;
      wstrb_q0  <=    wstrb;
      wlast_q0  <=    wlast;
      wuser_q0  <=    wuser;
      if (ROLE_BASED_USER) begin
          wuser_datachk_q0 <= wuser_datachk;
          wuser_poison_q0  <= wuser_poison;
          wuser_data_q0    <= wuser_data;
      end else begin
          wuser_datachk_q0 <= '0;
          wuser_poison_q0  <= '0;
          wuser_data_q0    <= '0;
      end
   end
end
 
 
// Read address channel
always @ (posedge aclk) begin
   if(read_cp_ready || ~arvalid_q0) begin
      arid_q0     <=     arid;
      araddr_q0   <=   araddr;
      arlen_q0    <=    arlen;
      arsize_q0   <=   arsize;
      arburst_q0  <=  arburst;
      arlock_q0   <=   arlock;
      arcache_q0  <=  arcache;
      arprot_q0   <=   arprot;
      arqos_q0    <=    arqos;
      arregion_q0 <= arregion;
      aruser_q0   <=   aruser;
      ardomain_q0 <= ardomain;
      arsnoop_q0  <=  arsnoop;
      arbar_q0    <=    arbar;
      if (ROLE_BASED_USER) begin
          aruser_addrchk_q0 <= aruser_addrchk;
          aruser_sai_q0 <= aruser_sai;
      end else begin
          aruser_addrchk_q0 <= '0; 
          aruser_sai_q0     <= '0;
      end
   end
end
   
generate 
if(ROLE_BASED_USER) begin
   wire [ADDRCHK_WIDTH-1:0]      expected_awuser_addrchk_parity; 
   wire [ADDRCHK_WIDTH-1:0]      expected_aruser_addrchk_parity; 
   
   if (SKIP_USER_ADDRCHK_CAL) begin
        assign expected_awuser_addrchk_parity = 1'b0;
        assign expected_aruser_addrchk_parity = 1'b0;

        assign aw_parity_status = 1'b0;
        assign ar_parity_status = 1'b0;
   end
   else begin
        assign expected_awuser_addrchk_parity = addrcalcParity ( {{PADDING_ZERO{1'b0}},awaddr_q0 });
        assign expected_aruser_addrchk_parity = addrcalcParity ( {{PADDING_ZERO{1'b0}},araddr_q0 });

        assign aw_parity_status = (expected_awuser_addrchk_parity == awuser_addrchk_q0) ? 1'b0 : 1'b1;
        assign ar_parity_status = (expected_aruser_addrchk_parity == aruser_addrchk_q0) ? 1'b0 : 1'b1;
   end 
end
else begin
   assign aw_parity_status = 1'b0;
   assign ar_parity_status = 1'b0;
end
endgenerate
 
 
//--------------------------------------
 
always_comb
    begin
        write_burst_type = burst_type_decode(awburst_q0);
        read_burst_type  = burst_type_decode(arburst_q0);
    end

//--------------------------------------
// Global signals
//--------------------------------------
wire [31:0] id_int      = ID;
 
//--------------------------------------
// Command control for write packet 
//--------------------------------------
// Handling address and data 
// 
// The master NI will only send a packet
// when it receives both address and data.
 
wire write_addr_data_both_valid;
 
assign write_addr_data_both_valid = awvalid_q0 && wvalid_q0;
assign network_ready = write_cp_ready;
 
 
//-------------------------
// Burst address and bytecount assignment
// ------------------------
reg [PKT_ADDR_W-1       : 0]    start_address;
reg [PKT_BYTE_CNT_W-1   : 0]    total_write_bytecount;
reg [PKT_BYTE_CNT_W-1   : 0]    total_read_bytecount;
reg [PKT_BYTE_CNT_W-1   : 0]    write_burst_bytecount;
 
reg [PKT_ADDR_W-1       : 0]    burst_address;
reg [PKT_BYTE_CNT_W-1   : 0]    burst_bytecount;
 
 
// Keep temporary address
reg     [PKT_BYTE_CNT_W-1 : 0]  total_bytecount_left;
 
reg    [31:0]                   total_write_bytecount_wire;  // to eliminate QIS warning
reg    [31:0]                   total_read_bytecount_wire;   // to eliminate QIS warning
reg    [31:0]                   total_bytecount_left_wire;   // to eliminate QIS warning
 
// First address and bytecount of a burst
always_comb
begin
    total_write_bytecount_wire  = (awlen_q0 + 1) << $clog2(NUMSYMBOLS);
    total_read_bytecount_wire   = (arlen_q0 + 1) << $clog2(NUMSYMBOLS);
    total_write_bytecount       = total_write_bytecount_wire[PKT_BYTE_CNT_W-1:0];
    total_read_bytecount        = total_read_bytecount_wire[PKT_BYTE_CNT_W-1:0];
    start_address               = awaddr_q0; 
end
 
//-----------------------------------------------------------------------
// The address_alignment is used to align address to size and increment burst address if needed
// it has input: {burswrap_boundary, start_addr, bursttype, burst_zize}
// return output is aligned address and increment if set, with Wrap the output address will wrap
// according to wrap boundary. Fixed burst, address will be kept same
// In case INCREMENT_ADDRESS = 0, the component acts as combinational logic and return algined address
// and a mask to algin address if wish to use.
//
// Refer for comments inside the component for more details
//-----------------------------------------------------------------------
    
reg [PKT_ADDR_W-1 : 0]  address_aligned;
reg [31 : 0]            burstwrap_value_write;
reg [31 : 0]            burstwrap_value_read;
 
    generate
        if (AXI_VERSION != "AXI4Lite") begin
          //--------------------------------------
          // Calculate the value of burstwrap for a wrapping burst. 
          // The algorithm figures out the width of the burstwrap 
          // boundary, and uses that to set a bit mask for burstwrap.
          //
          // This should synthesize to a small adder, followed by a 
          // per-bit comparator (which gets folded into the adder).
          //--------------------------------------
          reg     [PKT_BURSTWRAP_W - 2 : 0]       burstwrap_boundary_write;
          reg     [PKT_BURSTWRAP_W - 2 : 0]       burstwrap_boundary_read;
          wire    [31 : 0]                        burstwrap_boundary_width_write;
          wire    [31 : 0]                        burstwrap_boundary_width_read;
          
          reg     [PKT_ADDR_W-1 : 0]              incremented_burst_address;
          reg     [PKT_ADDR_W-1 : 0]              burstwrap_mask;
          reg     [PKT_ADDR_W-1 : 0]              burst_address_high;
          reg     [PKT_ADDR_W-1 : 0]              burst_address_low;
          reg [PKT_ADDR_W + (PKT_BURSTWRAP_W-1) + 4 : 0] address_for_alignment;
          reg [PKT_ADDR_W+$clog2(NUMSYMBOLS)-1 :0]  address_after_alignment;
          wire    [31:0]  bytes_in_transfer_minusone_write_wire;     // eliminates synthesis warning
          wire    [31:0]  bytes_in_transfer_minusone_read_wire;     // eliminates synthesis warning 
          
          assign burstwrap_boundary_width_write   =    awsize_q0 + log2ceil(awlen_q0 + 1);
          assign burstwrap_boundary_width_read    =    arsize_q0 + log2ceil(arlen_q0 + 1);
          
          function reg [PKT_BURSTWRAP_W - 2 : 0] burstwrap_boundary_calculation
          (
              input [31 : 0]  burstwrap_boundary_width,
              input int       width = PKT_BURSTWRAP_W - 1
          );
              integer i;
          
              burstwrap_boundary_calculation = 0;
              for (i = 0; i < width; i++) begin
                  if (burstwrap_boundary_width > i)
                      burstwrap_boundary_calculation[i] = 1;
              end
          
          endfunction 
          
          assign burstwrap_boundary_write = burstwrap_boundary_calculation(burstwrap_boundary_width_write, PKT_BURSTWRAP_W - 1);
          assign burstwrap_boundary_read  = burstwrap_boundary_calculation(burstwrap_boundary_width_read, PKT_BURSTWRAP_W - 1);
          
          //--------------------------------------
          // Use the burst type to set correct burstwrap value and address increment
          //--------------------------------------
          
          
          assign  bytes_in_transfer_minusone_write_wire = bytes_in_transfer(awsize_q0) - 1;
          assign  bytes_in_transfer_minusone_read_wire  = bytes_in_transfer(arsize_q0) - 1; 
          
          always_comb
          begin
              burstwrap_value_write = 0;
              case (write_burst_type)
                  INCR:    
                  begin
                      burstwrap_value_write[PKT_BURSTWRAP_W - 1 : 0]    = {PKT_BURSTWRAP_W {1'b1}};
                  end 
                  WRAP:
                  begin
                      burstwrap_value_write[PKT_BURSTWRAP_W - 1 : 0]    = {1'b0, burstwrap_boundary_write};
                  end
                  FIXED:
                  begin
                      burstwrap_value_write[PKT_BURSTWRAP_W - 1 : 0]    = bytes_in_transfer_minusone_write_wire[PKT_BURSTWRAP_W -1 : 0];
                  end
                  default:
                  begin
                      burstwrap_value_write[PKT_BURSTWRAP_W - 1 : 0]    = {PKT_BURSTWRAP_W {1'b1}};
                  end
              endcase
          end
          
          always_comb
          begin
              burstwrap_value_read = 0;
              case (read_burst_type)
                  INCR:    
                  begin
                      burstwrap_value_read[PKT_BURSTWRAP_W - 1 : 0] = {PKT_BURSTWRAP_W {1'b1}};
                  end 
                  WRAP:
                  begin
                      burstwrap_value_read[PKT_BURSTWRAP_W - 1 : 0] = {1'b0, burstwrap_boundary_read};
                  end
                  FIXED:
                  begin
                      burstwrap_value_read[PKT_BURSTWRAP_W - 1 : 0] = bytes_in_transfer_minusone_read_wire[PKT_BURSTWRAP_W -1 : 0];    
                  end
                  default:
                  begin
                      burstwrap_value_read[PKT_BURSTWRAP_W - 1 : 0] = {PKT_BURSTWRAP_W {1'b1}};
                  end
              endcase
          end
            assign address_aligned          = address_after_alignment[PKT_ADDR_W - 1 : 0];
            assign address_for_alignment  = {burstwrap_boundary_write,awburst_q0, start_address, awsize_q0};
 
            altera_merlin_address_alignment
                #(
                  .ADDR_W (PKT_ADDR_W),
                  .BURSTWRAP_W (PKT_BURSTWRAP_W),
                  .INCREMENT_ADDRESS (1),
                  .NUMSYMBOLS (NUMSYMBOLS),
                  .SYNC_RESET (SYNC_RESET)
                  ) align_address_to_size
            (
             .clk (aclk),
             .reset (aresetn),
             .in_data (address_for_alignment),
             .in_valid (write_addr_data_both_valid),
             .in_sop (write_cp_startofpacket),
             .in_eop (wlast_q0),
 
             .out_data (address_after_alignment),
             .out_ready (write_cp_ready)
             );
        end else begin
           assign address_aligned = start_address; 
        end
    endgenerate
    
     
// -----------------------------------------------------------------------------
 
// increase address and decrease bytecount
assign total_bytecount_left_wire    =   write_burst_bytecount - NUMSYMBOLS;
assign total_bytecount_left         =   total_bytecount_left_wire[PKT_BYTE_CNT_W-1:0];
 
always_comb
begin
    if (write_cp_startofpacket)
        begin
            write_burst_bytecount   =    total_write_bytecount;
        end
    else 
        begin
            write_burst_bytecount   =    burst_bytecount;
        end
end
 
generate
if (SYNC_RESET == 0) begin : async_rst0
  always_ff @(posedge aclk, negedge aresetn)
  begin
      if (!aresetn)
          begin
              burst_bytecount     <= {PKT_BYTE_CNT_W{1'b0}};
          end
      else
          begin
              if (write_addr_data_both_valid && write_cp_ready)
                  begin
                      burst_bytecount     <=    total_bytecount_left;
                  end
          end
  
  end
end : async_rst0  
 
else begin : sync_rst0  
  always_ff @(posedge aclk)
  begin
      if (internal_sclr)
          begin
              burst_bytecount     <= {PKT_BYTE_CNT_W{1'b0}};
          end
      else
          begin
              if (write_addr_data_both_valid && write_cp_ready)
                  begin
                      burst_bytecount     <=    total_bytecount_left;
                  end
          end
  
  end
end : sync_rst0
endgenerate
//------------------------------------------------------
// Generate startofpacket ~ beginbursttransfer
// -----------------------------------------------------
reg sop_enable;
 
generate
 if (SYNC_RESET == 0) begin : async_rst1
   always_ff @(posedge aclk, negedge aresetn)
   begin
       if (!aresetn)
           begin
               sop_enable <= 1'b1;
           end
       else
           begin
               // sop for write channel
               if (write_addr_data_both_valid && write_cp_ready)
                   begin
                       sop_enable <= 1'b0;
                       if (wlast_q0)
                           sop_enable <= 1'b1;
                   end
           end
   end
 end : async_rst1
 
 else begin : sync_rst1   
   always_ff @(posedge aclk)
   begin
       if (internal_sclr)
           begin
               sop_enable <= 1'b1;
           end
       else
           begin
               // sop for write channel
               if (write_addr_data_both_valid && write_cp_ready)
                   begin
                       sop_enable <= 1'b0;
                       if (wlast_q0)
                           sop_enable <= 1'b1;
                   end
           end
   end
 end : sync_rst1 
endgenerate          
assign write_cp_startofpacket       = sop_enable;
assign write_cp_endofpacket         = wlast_q0;   
assign read_cp_startofpacket        = 1'b1;
assign read_cp_endofpacket          = 1'b1;   
 
 
//--------------------------------------------------------
// AW/WREADY control
//
// Backpresure AWREADY until the data phase is complete
//--------------------------------------------------------
 
assign awready = awvalid_q0 ? (wvalid_q0 & wlast_q0 & network_ready) : 1'b1;
assign wready = wvalid_q0 ? (awvalid_q0 & network_ready) : 1'b1;
 
assign write_cp_valid    = write_addr_data_both_valid;
 
//--------------------------------------
// Command control for write response packet 
//--------------------------------------
assign bvalid            = write_rp_valid;
assign write_rp_ready    = bready;
 
//--------------------------------------
// Form write transaction packet
//--------------------------------------
always_comb  
    begin
        write_cp_data                                       = '0;
        write_cp_data[PKT_BYTE_CNT_H :PKT_BYTE_CNT_L ]      = write_burst_bytecount; 
        write_cp_data[PKT_TRANS_EXCLUSIVE            ]      = awlock_q0[0];
        write_cp_data[PKT_TRANS_LOCK                 ]      = '0;
        write_cp_data[PKT_TRANS_COMPRESSED_READ      ]      = '0;
        write_cp_data[PKT_TRANS_READ                 ]      = '0;
        write_cp_data[PKT_TRANS_WRITE                ]      = 1'b1; 
        write_cp_data[PKT_TRANS_POSTED               ]      = '0;
        write_cp_data[PKT_BURSTWRAP_H:PKT_BURSTWRAP_L]      = (AXI_VERSION == "AXI4Lite") ? 0 : burstwrap_value_write[PKT_BURSTWRAP_W - 1 : 0];
        write_cp_data[PKT_ADDR_H     :PKT_ADDR_L     ]      = address_aligned;
        write_cp_data[PKT_DATA_H     :PKT_DATA_L     ]      = wdata_q0;
        write_cp_data[PKT_BYTEEN_H   :PKT_BYTEEN_L   ]      = wstrb_q0;
        write_cp_data[PKT_BURST_SIZE_H :PKT_BURST_SIZE_L]   = awsize_q0;
        write_cp_data[PKT_BURST_TYPE_H :PKT_BURST_TYPE_L]   = awburst_q0;
        write_cp_data[PKT_SRC_ID_H   :PKT_SRC_ID_L   ]      = id_int[PKT_SRC_ID_W-1:0];
        write_cp_data[PKT_PROTECTION_H :PKT_PROTECTION_L]   = awprot_q0;
        write_cp_data[PKT_THREAD_ID_H :PKT_THREAD_ID_L]     = awid_q0;
        write_cp_data[PKT_CACHE_H :PKT_CACHE_L]             = awcache_q0;
        write_cp_data[PKT_ADDR_SIDEBAND_H:PKT_ADDR_SIDEBAND_L] = awuser_q0;
        write_cp_data[PKT_ORI_BURST_SIZE_H :PKT_ORI_BURST_SIZE_L] = awsize_q0;
        if (ROLE_BASED_USER) begin
            write_cp_data[PKT_POISON_H:PKT_POISON_L]            = wuser_poison_q0;
            write_cp_data[PKT_SAI_H:PKT_SAI_L]                  = awuser_sai_q0;        
            write_cp_data[PKT_USER_DATA_H:PKT_USER_DATA_L]      = wuser_data_q0;
            if(USE_PKT_DATACHK == 0)
                    write_cp_data[PKT_DATACHK_H:PKT_DATACHK_L]          = '0;               
            else
                    write_cp_data[PKT_DATACHK_H:PKT_DATACHK_L]          = wuser_datachk_q0;
            if(USE_PKT_ADDRCHK == 0)
                    write_cp_data[PKT_ADDRCHK_H:PKT_ADDRCHK_L]          = '0;               
            else
                    write_cp_data[PKT_ADDRCHK_H:PKT_ADDRCHK_L]          = {aw_parity_status,awuser_addrchk_q0};        
        end
 
        if(ACE_LITE_SUPPORT == 1) begin
            write_cp_data[PKT_DOMAIN_H : PKT_DOMAIN_L] = awdomain_q0;
            write_cp_data[PKT_SNOOP_H : PKT_SNOOP_L]   = {1'b0, awsnoop_q0};  // For consistency between write and read packets
            write_cp_data[PKT_BARRIER_H : PKT_BARRIER_L]       = awbar_q0;
            write_cp_data[PKT_WUNIQUE]                 = awunique_q0;
        end
        else begin
            write_cp_data[PKT_DOMAIN_H : PKT_DOMAIN_L] = 2'b11;    // System Domain
            write_cp_data[PKT_SNOOP_H : PKT_SNOOP_L]   = {1'b0, 3'b000};  // Cache maintenance transactions not supported
            write_cp_data[PKT_BARRIER_H : PKT_BARRIER_L]       = 2'b00;    // Not supported. ?? Check if 10 is suitable
            write_cp_data[PKT_WUNIQUE]                 = 'b0;
        end
        
        //  AXI4 signals: receive from the translator
        if (AXI_VERSION == "AXI4") begin
            write_cp_data[PKT_QOS_H : PKT_QOS_L]                     = awqos_q0;
            write_cp_data[PKT_DATA_SIDEBAND_H : PKT_DATA_SIDEBAND_L] = wuser_q0;
        end else begin //AXI3: set with default value
            write_cp_data[PKT_QOS_H : PKT_QOS_L]                     = '0;
            write_cp_data[PKT_DATA_SIDEBAND_H : PKT_DATA_SIDEBAND_L] = '0;
        end
        
        // Receive Response packet from the Slave
        bresp = write_rp_data[PKT_RESPONSE_STATUS_H : PKT_RESPONSE_STATUS_L];
        bid   = write_rp_data[PKT_THREAD_ID_H : PKT_THREAD_ID_L];
        // AXI4 signals
        buser = write_rp_data[PKT_DATA_SIDEBAND_H : PKT_DATA_SIDEBAND_L];
    end
 
//--------------------------------------
// Form read transaction packet 
//--------------------------------------
always_comb  
    begin
        read_cp_data                                        = '0;
        read_cp_data[PKT_BYTE_CNT_H :PKT_BYTE_CNT_L ]       = total_read_bytecount;
        read_cp_data[PKT_TRANS_EXCLUSIVE            ]       = arlock_q0[0];
        read_cp_data[PKT_TRANS_LOCK                 ]       = '0;
        if (AXI_VERSION != "AXI4Lite") begin
            read_cp_data[PKT_TRANS_COMPRESSED_READ] = 1'b1;
        end else begin
            read_cp_data[PKT_TRANS_COMPRESSED_READ] = '0;
        end
        read_cp_data[PKT_TRANS_READ                 ]       = '1;
        read_cp_data[PKT_TRANS_WRITE                ]       = '0;
        read_cp_data[PKT_TRANS_POSTED               ]       = '0;
        read_cp_data[PKT_BURSTWRAP_H:PKT_BURSTWRAP_L]       = (AXI_VERSION == "AXI4Lite") ? 0 : burstwrap_value_read[PKT_BURSTWRAP_W - 1 : 0];
        read_cp_data[PKT_ADDR_H     :PKT_ADDR_L     ]       = araddr_q0;
        read_cp_data[PKT_DATA_H     :PKT_DATA_L     ]       = '0;
        read_cp_data[PKT_BYTEEN_H   :PKT_BYTEEN_L   ]       = {PKT_BYTEEN_W{1'b1}};
        read_cp_data[PKT_SRC_ID_H   :PKT_SRC_ID_L   ]       = id_int[PKT_SRC_ID_W-1:0];
        read_cp_data[PKT_BURST_SIZE_H :PKT_BURST_SIZE_L]    = arsize_q0;
        read_cp_data[PKT_ORI_BURST_SIZE_H :PKT_ORI_BURST_SIZE_L] = arsize_q0;
        read_cp_data[PKT_BURST_TYPE_H :PKT_BURST_TYPE_L]    = arburst_q0;
        read_cp_data[PKT_PROTECTION_H : PKT_PROTECTION_L]   = arprot_q0;
        read_cp_data[PKT_THREAD_ID_H  : PKT_THREAD_ID_L]    = arid_q0;
        read_cp_data[PKT_CACHE_H  : PKT_CACHE_L]            = arcache_q0;
 
        read_cp_data[PKT_ADDR_SIDEBAND_H:PKT_ADDR_SIDEBAND_L] = aruser_q0;
        read_cp_data[PKT_DATA_SIDEBAND_H : PKT_DATA_SIDEBAND_L] = '0;
 
        // AXI4 signals: receive from translator
        if (AXI_VERSION == "AXI4") begin
            read_cp_data[PKT_QOS_H : PKT_QOS_L]                     = arqos_q0;
        end else begin
            read_cp_data[PKT_QOS_H : PKT_QOS_L]                     = '0;
        end
 
        if(ROLE_BASED_USER) begin
            read_cp_data[PKT_SAI_H:PKT_SAI_L]                   = aruser_sai_q0;
            if(USE_PKT_ADDRCHK == 0)
               read_cp_data[PKT_ADDRCHK_H : PKT_ADDRCHK_L ]   = '0;
            else         
               read_cp_data [PKT_ADDRCHK_H   : PKT_ADDRCHK_L ] = {ar_parity_status,aruser_addrchk_q0};           
        end
 
            if(ACE_LITE_SUPPORT == 1) begin
                read_cp_data[PKT_DOMAIN_H : PKT_DOMAIN_L] = ardomain_q0;
                read_cp_data[PKT_SNOOP_H : PKT_SNOOP_L]   = arsnoop_q0;
                read_cp_data[PKT_BARRIER_H : PKT_BARRIER_L] = arbar_q0;
                read_cp_data[PKT_WUNIQUE]                 = 'b0;      // Does not exist in read channel
            end
            else begin
                read_cp_data[PKT_DOMAIN_H : PKT_DOMAIN_L] = 2'b11;    // System Domain
                read_cp_data[PKT_SNOOP_H : PKT_SNOOP_L]   = 4'b0000;  // Cache maintenance transactions not supported
                read_cp_data[PKT_BARRIER_H : PKT_BARRIER_L] = 2'b00;  // Not supported. ?? Check if 10 is suitable
                read_cp_data[PKT_WUNIQUE]                 = 'b0;
            end
            
            // Read data packet from the Slave, connect to rdata
            rdata    = read_rp_data[PKT_DATA_H     :PKT_DATA_L];
            rresp    = read_rp_data[PKT_RESPONSE_STATUS_H : PKT_RESPONSE_STATUS_L];
            rid      = read_rp_data[PKT_THREAD_ID_H : PKT_THREAD_ID_L];
            // AXI4 signals
            ruser    = read_rp_data[PKT_DATA_SIDEBAND_H : PKT_DATA_SIDEBAND_L];
            //AXI4 role based user signals
            if(ROLE_BASED_USER) begin
            ruser_poison   = read_rp_data[PKT_POISON_H : PKT_POISON_L];
            ruser_data     = read_rp_data[PKT_USER_DATA_H : PKT_USER_DATA_L];
            if (USE_PKT_DATACHK==0)
               ruser_datachk  = calcParity(read_rp_data[PKT_DATA_H:PKT_DATA_L]);
            else
               ruser_datachk  = read_rp_data[PKT_DATACHK_H : PKT_DATACHK_L];
 
            end
    end
 
//--------------------------------------
// Command control for read packets
//--------------------------------------
assign    read_cp_valid                 = arvalid_q0;
assign    arready                       = read_cp_ready || ~arvalid_q0;
 
//--------------------------------------
// Command for handling read data
//--------------------------------------
assign rvalid                   = read_rp_valid;
assign read_rp_ready            = rready;
assign rlast                    = read_rp_endofpacket;
 
//--------------------------------------
// Assertions
//--------------------------------------
// synthesis translate_off
    generate
        if (WRITE_ISSUING_CAPABILITY == 1) begin
            wire write_cmd_accepted;
            wire write_response_accepted;
            wire write_response_count_is_1;
            reg [$clog2(WRITE_ISSUING_CAPABILITY+1)-1:0] pending_write_response_count;
            reg [$clog2(WRITE_ISSUING_CAPABILITY+1)-1:0] next_pending_write_response_count;
    
            assign write_cmd_accepted  = write_cp_valid && write_cp_ready && write_cp_endofpacket;
            assign write_response_accepted  = write_rp_valid && write_rp_ready && write_rp_endofpacket;
    
            always_comb
                begin
                    next_pending_write_response_count  = pending_write_response_count;
                    if (write_cmd_accepted)
                        next_pending_write_response_count  = pending_write_response_count + 1'b1;
                    if (write_response_accepted)
                        next_pending_write_response_count  = pending_write_response_count - 1'b1;
                    if (write_cmd_accepted && write_response_accepted)
                        next_pending_write_response_count  = pending_write_response_count;
                end
 
            if (SYNC_RESET == 0) begin : async_rst2
               always_ff @(posedge aclk, negedge aresetn)
                   begin
                       if (!aresetn) begin
                           pending_write_response_count <= '0;
                       end else begin
                           pending_write_response_count <= next_pending_write_response_count;
                       end
                   end
            end : async_rst2
 
            else begin : sync_rst2    
               always_ff @(posedge aclk)
                   begin
                       if (internal_sclr) begin
                           pending_write_response_count <= '0;
                       end else begin
                           pending_write_response_count <= next_pending_write_response_count;
                       end
                   end
            end : sync_rst2   
 
            
            assign write_response_count_is_1  = (pending_write_response_count == 1);
            // assertion
            ERROR_WRITE_ISSUING_CAPABILITY_equal_1_but_master_sends_more_commands_or_switch_slave_before_response_back_please_visit_the_parameter:
                assert property (@(posedge aclk)
                    disable iff (!aresetn || $isunknown(aresetn)) !(write_response_count_is_1 && write_cmd_accepted));
            end // if (WRITE_ISSUING_CAPABILITY == 1)
        
        if (READ_ISSUING_CAPABILITY == 1) begin
            wire read_cmd_accepted;
            wire read_response_accepted;
            wire read_response_count_is_1;
    
            reg [$clog2(READ_ISSUING_CAPABILITY+1)-1:0]  pending_read_response_count;
            reg [$clog2(READ_ISSUING_CAPABILITY+1)-1:0]  next_pending_read_response_count;
    
            assign read_cmd_accepted  = read_cp_valid && read_cp_ready && read_cp_endofpacket;
            assign read_response_accepted  = read_rp_valid && read_rp_ready && read_rp_endofpacket;
    
            always_comb
                begin
                    next_pending_read_response_count   = pending_read_response_count;
                    if (read_cmd_accepted)
                        next_pending_read_response_count  = pending_read_response_count + 1'b1;
                    if (read_response_accepted)
                        next_pending_read_response_count  = pending_read_response_count - 1'b1;
                    if (read_cmd_accepted && read_response_accepted)
                        next_pending_read_response_count  = pending_read_response_count;
                end
 
            if (SYNC_RESET == 0) begin : async_rst3
              always_ff @(posedge aclk, negedge aresetn)
                  begin
                      if (!aresetn) begin
                          pending_read_response_count  <= '0;
                      end else begin
                          pending_read_response_count  <= next_pending_read_response_count;
                      end
                  end
            end : async_rst3
 
            else begin : sync_rst3 
              always_ff @(posedge aclk)
                  begin
                      if (internal_sclr) begin
                          pending_read_response_count  <= '0;
                      end else begin
                          pending_read_response_count  <= next_pending_read_response_count;
                      end
                  end // @always
            end : sync_rst3
            assign read_response_count_is_1 = (pending_read_response_count == 1);
            ERROR_READ_ISSUING_CAPABILITY_equal_1_but_master_sends_more_commands_or_switch_slave_before_response_back_please_visit_the_parameter:
                assert property (@(posedge aclk)
                    disable iff (!aresetn || $isunknown(aresetn)) !(read_response_count_is_1 && read_cmd_accepted));
        end // if (READ_ISSUING_CAPABILITY == 1)
    endgenerate
 
// This generate blocks disables the assertion for first 16 clock cycles
    generate 
    reg[4:0] count;
 
        always @ (posedge aclk, negedge aresetn)
            begin
                if (!aresetn) begin
                    count <= '0;
                end
                else begin
                    if (count < 20) begin
                        count <= count + 1'b1;
                    end
                    else begin
                        count <= count;
                    end
                end
            end
 
        always @(*) 
            begin 
                if (count >= 15) begin
                   ERROR_awlock_reserved_value:
                       assert property (@(posedge aclk)
                           disable iff (!aresetn || $isunknown(aresetn)) ( !(awvalid_q0 && awlock_q0 == 2'b11) ));
 
                   ERROR_arlock_reserved_value:
                       assert property (@(posedge aclk)
                           disable iff (!aresetn || $isunknown(aresetn)) ( !(arvalid_q0 && arlock_q0 == 2'b11) ));
                end
            end
    endgenerate
// synthesis translate_on

//address parity generation logic 
    function reg [ADDRCHK_WIDTH-1:0] addrcalcParity (
        input [PARITY_ADDR_WIDTH-1:0] addr
    );
        for (int i=0; i<ADDRCHK_WIDTH; i++)
            addrcalcParity[i] = ~(^ addr[i*8 +:8]);
    endfunction


endmodule


