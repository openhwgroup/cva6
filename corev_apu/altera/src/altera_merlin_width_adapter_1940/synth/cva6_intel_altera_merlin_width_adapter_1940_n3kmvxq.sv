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


// $Id: //acds/main/ip/merlin/altera_merlin_width_adapter/altera_merlin_width_adapter.sv#66 $
// $Revision: #66 $
// $Date: 2018/07/06 $ 

// -----------------------------------------------------
// Merlin Width Adapter
// -----------------------------------------------------

`timescale 1 ns / 1 ns

module cva6_intel_altera_merlin_width_adapter_1940_n3kmvxq 
#(
    parameter IN_PKT_ADDR_L                 = 0,
    parameter IN_PKT_ADDR_H                 = 31,
    parameter IN_PKT_DATA_L                 = 32,
    parameter IN_PKT_DATA_H                 = 63,
    parameter IN_PKT_BYTEEN_L               = 64,
    parameter IN_PKT_BYTEEN_H               = 67,
    parameter IN_PKT_TRANS_COMPRESSED_READ  = 72,
    parameter IN_PKT_BYTE_CNT_L             = 73,
    parameter IN_PKT_BYTE_CNT_H             = 77,
    parameter IN_PKT_BURSTWRAP_L            = 78,
    parameter IN_PKT_BURSTWRAP_H            = 82,
    parameter IN_PKT_BURST_SIZE_L           = 83,
    parameter IN_PKT_BURST_SIZE_H           = 85,
    parameter IN_PKT_RESPONSE_STATUS_L      = 86,
    parameter IN_PKT_RESPONSE_STATUS_H      = 87,
    parameter IN_PKT_TRANS_EXCLUSIVE        = 88,
    parameter IN_PKT_BURST_TYPE_L           = 89,
    parameter IN_PKT_BURST_TYPE_H           = 90,
    parameter IN_PKT_ORI_BURST_SIZE_L       = 91,
    parameter IN_PKT_ORI_BURST_SIZE_H       = 93,
    parameter IN_PKT_TRANS_WRITE            = 94,
    //AXI5Lite Parameters
    parameter IN_PKT_POISON_L               = 95,
    parameter IN_PKT_POISON_H               = 96,
    parameter IN_PKT_DATACHK_L              = 97,
    parameter IN_PKT_DATACHK_H              = 104,
    parameter IN_PKT_ADDRCHK_L              = 105,
    parameter IN_PKT_ADDRCHK_H              = 108,
    parameter IN_PKT_SAI_L                  = 109,
    parameter IN_PKT_SAI_H                  = 112,    
    parameter IN_PKT_USER_DATA_L            = 113, 
    parameter IN_PKT_USER_DATA_H            = 113, 
    parameter IN_ST_DATA_W                  = 134,

    parameter OUT_PKT_ADDR_L                = 0,
    parameter OUT_PKT_ADDR_H                = 31,
    parameter OUT_PKT_DATA_L                = 32,
    parameter OUT_PKT_DATA_H                = 47,
    parameter OUT_PKT_BYTEEN_L              = 48,
    parameter OUT_PKT_BYTEEN_H              = 49,
    parameter OUT_PKT_TRANS_COMPRESSED_READ = 54,
    parameter OUT_PKT_BYTE_CNT_L            = 55,
    parameter OUT_PKT_BYTE_CNT_H            = 59,
    parameter OUT_PKT_BURST_SIZE_L          = 60,
    parameter OUT_PKT_BURST_SIZE_H          = 62,
    parameter OUT_PKT_RESPONSE_STATUS_L     = 63,
    parameter OUT_PKT_RESPONSE_STATUS_H     = 64,
    parameter OUT_PKT_TRANS_EXCLUSIVE       = 65,
    parameter OUT_PKT_BURST_TYPE_L          = 66,
    parameter OUT_PKT_BURST_TYPE_H          = 67,
    parameter OUT_PKT_ORI_BURST_SIZE_L      = 68,
    parameter OUT_PKT_ORI_BURST_SIZE_H      = 70,
    //AXI5 Lite Parameters
    parameter OUT_PKT_POISON_L              = 71,
    parameter OUT_PKT_POISON_H              = 71,
    parameter OUT_PKT_DATACHK_L             = 72,
    parameter OUT_PKT_DATACHK_H             = 75,
    parameter OUT_PKT_ADDRCHK_L             = 76,
    parameter OUT_PKT_ADDRCHK_H             = 79,
    parameter OUT_PKT_SAI_L                 = 80,
    parameter OUT_PKT_SAI_H                 = 83,
    parameter OUT_PKT_EOP_OOO               = 84,
    parameter OUT_PKT_SOP_OOO               = 85,    
    parameter OUT_PKT_USER_DATA_L           = 86, 
    parameter OUT_PKT_USER_DATA_H           = 87, 
    parameter OUT_ST_DATA_W                 = 88,

    parameter ROLE_BASED_USER               = 0,
    parameter BITSPERBYTE                   = 0,
    parameter ENABLE_OOO                    = 0,

    parameter ST_CHANNEL_W                  = 32,
    parameter OPTIMIZE_FOR_RSP              = 0,

    parameter PACKING                       = 1,    // 1: Enables packing in Avalon systems
    parameter CONSTANT_BURST_SIZE           = 1,    // 1: Optimizes for Avalon-only systems as those always have full size transactions
    parameter RESPONSE_PATH                 = 0,    // 0: This adapter is on command path, 1: This adapter is on response path

    // Address alignment can be turned off (an optimisation) if all connected
    // masters only issue aligned addresses.
    parameter ENABLE_ADDRESS_ALIGNMENT      = 1,
    parameter SYNC_RESET                    = 0
)
( 
    input                            clk,
    input                            reset,
    output reg                       in_ready,
    input                            in_valid,
    input      [ST_CHANNEL_W-1:0]    in_channel,
    input      [IN_ST_DATA_W-1:0]    in_data,
    input                            in_startofpacket,
    input                            in_endofpacket,
    input                            out_ready,
    output reg                       out_valid,
    output reg [ST_CHANNEL_W-1:0]    out_channel,
    output reg [OUT_ST_DATA_W-1:0]   out_data,
    output reg                       out_startofpacket,
    output reg                       out_endofpacket,

    input      [2:0]                 in_command_size_data
);

    // ------------------------------------------------------------
    // Local Parameters
    // ------------------------------------------------------------
    localparam IN_NUMSYMBOLS        = IN_PKT_BYTEEN_H - IN_PKT_BYTEEN_L + 1;
    localparam IN_DATA_W            = IN_PKT_DATA_H   - IN_PKT_DATA_L   + 1;
    localparam IN_BYTEEN_W          = IN_NUMSYMBOLS;

    localparam OUT_NUMSYMBOLS       = OUT_PKT_BYTEEN_H - OUT_PKT_BYTEEN_L + 1;
    localparam OUT_DATA_W           = OUT_PKT_DATA_H   - OUT_PKT_DATA_L   + 1;
    localparam OUT_BYTEEN_W         = OUT_NUMSYMBOLS;

    localparam BURST_TYPE_W         = IN_PKT_BURST_TYPE_H - IN_PKT_BURST_TYPE_L + 1;
    localparam BURST_SIZE_W         = IN_PKT_BURST_SIZE_H - IN_PKT_BURST_SIZE_L + 1;    
    localparam RESPONSE_STATUS_W    = IN_PKT_RESPONSE_STATUS_H - IN_PKT_RESPONSE_STATUS_L + 1;
    localparam SYMBOL_W             = IN_DATA_W / IN_NUMSYMBOLS;
    localparam ADDRESS_W            = IN_PKT_ADDR_H     - IN_PKT_ADDR_L     + 1;
    localparam BYTE_CNT_W           = IN_PKT_BYTE_CNT_H - IN_PKT_BYTE_CNT_L + 1;
    localparam OUT_BYTE_CNT_W       = OUT_PKT_BYTE_CNT_H - OUT_PKT_BYTE_CNT_L + 1;
    localparam BWRAP_W              = IN_PKT_BURSTWRAP_H - IN_PKT_BURSTWRAP_L + 1;
    localparam SIZE_W               = 2 ** BURST_SIZE_W;

    localparam RATIO                = (IN_NUMSYMBOLS > OUT_NUMSYMBOLS ? 
                                         IN_NUMSYMBOLS / OUT_NUMSYMBOLS : 
                                         OUT_NUMSYMBOLS / IN_NUMSYMBOLS );
    localparam WIDE_NUMSYMBOLS      = (IN_NUMSYMBOLS > OUT_NUMSYMBOLS ? 
                                         IN_NUMSYMBOLS : OUT_NUMSYMBOLS );
    localparam WIDE_DATA            = (IN_NUMSYMBOLS > OUT_NUMSYMBOLS ? 
                                         IN_DATA_W - (OUT_NUMSYMBOLS*SYMBOL_W) : 
                                         OUT_DATA_W - (IN_NUMSYMBOLS*SYMBOL_W));
    localparam OUT_SEGMENT_W        = OUT_NUMSYMBOLS * SYMBOL_W;

    localparam NW_BITFORSELECT_R    = clogb2(IN_NUMSYMBOLS);
    localparam NW_BITFORSELECT_L    = clogb2(OUT_NUMSYMBOLS) - 1;
    localparam ALIGNED_BITS_L       = clogb2(OUT_NUMSYMBOLS) - 1;
    localparam WN_ADDR_LSBS         = clogb2(RATIO);
    localparam WN_ADDR_SELECT       = clogb2(IN_NUMSYMBOLS);
    localparam LOG_OUT_NUMSYMBOLS   = clogb2(OUT_NUMSYMBOLS);
    
    localparam IN_POISON_W          = IN_PKT_POISON_H   - IN_PKT_POISON_L + 1;
    localparam OUT_POISON_W         = OUT_PKT_POISON_H - OUT_PKT_POISON_L + 1;
    
    localparam IN_SAI_W             = IN_PKT_SAI_H   - IN_PKT_SAI_L + 1;
    localparam OUT_SAI_W            = OUT_PKT_SAI_H  -  OUT_PKT_SAI_L + 1;  
   
    localparam IN_ADDRCHK_W         = IN_PKT_ADDRCHK_H   - IN_PKT_ADDRCHK_L + 1;
    localparam OUT_ADDRCHK_W        = OUT_PKT_ADDRCHK_H  -  OUT_PKT_ADDRCHK_L + 1;     

    localparam IN_DATACHK_W         = IN_PKT_DATACHK_H   - IN_PKT_DATACHK_L + 1;
    localparam OUT_DATACHK_W        = OUT_PKT_DATACHK_H - OUT_PKT_DATACHK_L + 1;  
    localparam WIDE_DATACHK         = (IN_NUMSYMBOLS > OUT_NUMSYMBOLS ? IN_DATACHK_W : OUT_DATACHK_W );    
    
    localparam POISON_W             = (IN_NUMSYMBOLS > OUT_NUMSYMBOLS ) ? (IN_POISON_W - OUT_POISON_W ) : (OUT_POISON_W - IN_POISON_W);

    localparam IN_USER_DATA_W       = IN_PKT_USER_DATA_H   - IN_PKT_USER_DATA_L   + 1;
    localparam USER_DATA_SYMBOL_W   = max(1, IN_USER_DATA_W / IN_NUMSYMBOLS);
    localparam OUT_USER_DATA_SEGMENT_W        = OUT_NUMSYMBOLS * USER_DATA_SYMBOL_W;
    localparam OUT_USER_DATA_W         = OUT_PKT_USER_DATA_H - OUT_PKT_USER_DATA_L + 1;
    localparam WIDE_USER_DATA          = (IN_NUMSYMBOLS > OUT_NUMSYMBOLS ? 
                                         IN_USER_DATA_W - (OUT_NUMSYMBOLS*USER_DATA_SYMBOL_W) : 
                                         OUT_USER_DATA_W - (IN_NUMSYMBOLS*USER_DATA_SYMBOL_W));

    
    // ------------------------------------------------------------
    // Utility Functions
    // ------------------------------------------------------------

    function integer clogb2;
        input [63:0] value;
        begin
            clogb2 = 0;
            while (value>0) begin
                value = value >> 1;
                clogb2 = clogb2 + 1;
            end
            clogb2 = clogb2 - 1;
        end
    endfunction // clogb2    

    function integer min;
        input [31:0] a;
        input [31:0] b;
        begin
            return (a < b) ? a : b;
        end
    endfunction

    function integer max;
        input [31:0] a;
        input [31:0] b;
        begin
            return (a > b) ? a : b;
        end
    endfunction

    function reg [clogb2(RATIO)-1:0] mask_to_select_correct_segments_for_size;
        input [clogb2(RATIO)-1:0] select_output_segment;
        input [9:0]     size_ratio;
        input int       msb_select_bit;

        integer         i;
        mask_to_select_correct_segments_for_size    = '1;
        for (i=0; i < msb_select_bit; i = i +1'b1 ) begin
            if (clogb2(size_ratio) > i)
                mask_to_select_correct_segments_for_size[i]   = select_output_segment[i];
        end
    endfunction 
  
    function reg [ADDRESS_W-1:0] choose_packed_address_base_on_size;
        input [9:0]     size_ratio;
        input int       msb_select_bit;
        
        integer         i;
        choose_packed_address_base_on_size = '1;
        for (i=0; i < msb_select_bit; i = i +1'b1 ) begin
            if (clogb2(size_ratio) > i)
                choose_packed_address_base_on_size[i + NW_BITFORSELECT_R]    = 1'b0;
        end
    endfunction

    // ------------------------------------------------------------
    // Computes how many bytes are in this transfer, based on the size
    // encoding.
    // ------------------------------------------------------------
    function reg[9:0] bytes_in_transfer;
        input [BURST_SIZE_W-1:0] axsize;
    
        case (axsize)
            4'b0000: bytes_in_transfer = 10'b0000000001;
            4'b0001: bytes_in_transfer = 10'b0000000010;
            4'b0010: bytes_in_transfer = 10'b0000000100;
            4'b0011: bytes_in_transfer = 10'b0000001000;
            4'b0100: bytes_in_transfer = 10'b0000010000;
            4'b0101: bytes_in_transfer = 10'b0000100000;
            4'b0110: bytes_in_transfer = 10'b0001000000;
            4'b0111: bytes_in_transfer = 10'b0010000000;
            4'b1000: bytes_in_transfer = 10'b0100000000;
            4'b1001: bytes_in_transfer = 10'b1000000000;            
            default: bytes_in_transfer = 10'b0000000001;
        endcase

    endfunction

    // ------------------------------------------------------------
    // Pseudo-field Parameters
    //
    // The width adapter widens the data and byteenable fields in the 
    // output packet, thus changing the output packet format. By using 
    // pseudo-fields, we can avoid remapping each individual field to 
    // the output, which is a non-scalable solution. 
    //
    // How? Assume the packet format is { FIRST, byteen, MID, data, LAST },
    // where byteen and data positions are interchangeable. FIRST, MID and
    // LAST are pseudo-fields that represent the collection of fields in
    // those positions.
    // 
    // Not all the pseudo-fields may exist for a given packet format. A
    // non-existent field has reversed indices, so we have to be careful 
    // when using them.
    // ------------------------------------------------------------

    localparam IN_FIRST_L   = 0,
               IN_FIRST_H   = min(IN_PKT_BYTEEN_L, IN_PKT_DATA_L) - 1,
               IN_MID_L     = min(IN_PKT_DATA_H, IN_PKT_BYTEEN_H) + 1,
               IN_MID_H     = max(IN_PKT_DATA_L, IN_PKT_BYTEEN_L) - 1,
               IN_LAST_L    = max(IN_PKT_BYTEEN_H, IN_PKT_DATA_H) + 1,
               IN_LAST_H    = IN_ST_DATA_W - 1,
 
               FIRST_EXISTS = (IN_FIRST_H >= IN_FIRST_L),
               MID_EXISTS   = (IN_MID_H   >= IN_MID_L),
               LAST_EXISTS  = (IN_LAST_H  >= IN_LAST_L),

               FIRST_W      = IN_FIRST_H - IN_FIRST_L + 1,
               MID_W        = IN_MID_H   - IN_MID_L   + 1,
               LAST_W       = IN_LAST_H  - IN_LAST_L  + 1,

               // -------------------------------------------------
               // We cannot split the output map into generate blocks as we
               // do for the inputs because address and size are mapped over
               // the pseudo-fields. We ensure that the indices are always
               // legal, even if the field is unused later on.

               OUT_FIRST_L = 0,
               OUT_FIRST_H = FIRST_EXISTS ? 
                                min(OUT_PKT_BYTEEN_L, OUT_PKT_DATA_L) - 1 :
                                OUT_FIRST_L,
               OUT_MID_L   = min(OUT_PKT_DATA_H, OUT_PKT_BYTEEN_H) + 1,
               OUT_MID_H   = MID_EXISTS ? 
                                max(OUT_PKT_DATA_L, OUT_PKT_BYTEEN_L) - 1 : 
                                OUT_MID_L,
               OUT_LAST_L  = max(OUT_PKT_BYTEEN_H, OUT_PKT_DATA_H) + 1,
               OUT_LAST_H  = LAST_EXISTS ? (OUT_ST_DATA_W - 1) : OUT_LAST_L;

    // ------------------------------------------------------------
    // Signals
    // ------------------------------------------------------------
    reg [BURST_SIZE_W-1:0]      in_size_field; 
    reg [IN_DATA_W-1:0]         in_data_field; 
    reg [IN_BYTEEN_W-1:0]       in_byteen_field;
    reg [ADDRESS_W-1:0]         in_address_field;
    reg [ADDRESS_W-1:0]         address_from_packet;
    reg [BYTE_CNT_W-1:0]        in_byte_cnt_field;
    reg [BWRAP_W-1:0]           in_burstwrap_field;
    reg [RESPONSE_STATUS_W-1:0] in_response_status_field;
    reg                         in_cmpr_read;
    reg                         in_lock_field;
    reg                         in_write;
    reg [BURST_TYPE_W-1:0]      in_burst_type_field;
    reg [BYTE_CNT_W-1:0]        quantized_byte_cnt_field;
    //AXI5Lite Poison 
    reg [IN_POISON_W-1 : 0 ]    in_poison_field;
    reg [IN_DATACHK_W-1 : 0]    in_datachk_field;
    reg [IN_SAI_W-1 : 0 ]       in_sai_field;
    reg [IN_ADDRCHK_W-1:0]      in_addrchk_field; 
    reg [IN_USER_DATA_W-1:0]    in_user_data_field; 
                                
    reg [BURST_SIZE_W-1:0]      out_size_field;
    reg [OUT_DATA_W-1:0]        out_data_field;
    reg [OUT_BYTEEN_W-1:0]      out_byteen_field;
    reg [ADDRESS_W-1:0]         out_address_field;
    reg                         out_cmpr_read;
    reg [BYTE_CNT_W-1:0]        out_byte_cnt_field;
    reg                         out_lock_field;
    reg [BURST_TYPE_W-1:0]      out_burst_type_field;
    reg [RESPONSE_STATUS_W-1:0] out_response_status_field;
    //AXI5Lite Poison 
    reg [OUT_POISON_W-1 : 0 ]   out_poison_field;
    reg [OUT_DATACHK_W-1: 0]    out_datachk_field;
    reg [OUT_SAI_W-1 : 0 ]      out_sai_field;
    reg [OUT_ADDRCHK_W-1 : 0]   out_addrchk_field;
    reg [OUT_USER_DATA_W-1:0]   out_user_data_field; 
    
    reg [FIRST_W-1:0]           in_first_field;
    reg [FIRST_W-1:0]           out_first_field;
    reg [MID_W-1:0]             in_mid_field;
    reg [MID_W-1:0]             out_mid_field;
    reg [LAST_W-1:0]            in_last_field;
    reg [LAST_W-1:0]            out_last_field;
    
    reg [OUT_SAI_W-1:0]         sai_reg;   
    reg [WIDE_DATACHK-1:0]      datachk_reg;    
    reg [OUT_DATACHK_W-1:0]     datachk_array[0:RATIO-1];    
    reg [WIDE_DATA-1:0]         data_reg;
    reg [WIDE_USER_DATA-1:0]    user_data_reg;
    reg [WIDE_NUMSYMBOLS-1:0]   byteen_reg;
    reg [ADDRESS_W-1:0]         address_reg;
    reg [BYTE_CNT_W-1:0]        byte_cnt_reg;
    reg                         use_reg;
    reg                         startofpacket_reg;
    reg                         endofpacket_reg;
    reg [OUT_SEGMENT_W-1:0]     mask;
    reg [OUT_USER_DATA_SEGMENT_W-1:0]     user_data_mask;
    reg [RESPONSE_STATUS_W-1:0] response_status_reg;
    
    
    reg [ADDRESS_W-1:0]         int_output_sel;
    reg [clogb2(RATIO)-1:0]     output_sel;
    reg [OUT_SEGMENT_W-1:0]     data_array   [0:RATIO-1];
    reg [OUT_USER_DATA_SEGMENT_W-1:0]     user_data_array   [0:RATIO-1];
    reg [OUT_NUMSYMBOLS-1:0]    byteen_array [0:RATIO-1];
        

    // In narrow-to-wide adaptation, each input datum/byteenable bit maps to
    // one of OUT_NUMSYMBOLS/IN_NUMSYMBOLS subfields in the wider output
    // packet. (Call these subfields "segments".)  A subfield of the input
    // address, in_bitforselect, selects the segment. Examples:
    // 8-16 adaptation:  in_bitforselect = in_address_field[0]
    // 8-32 adaptation:  in_bitforselect = in_address_field[1:0]
    // 8-64 adaptation:  in_bitforselect = in_address_field[2:0]
    // 16-32 adaptation: in_bitforselect = in_address_field[1]
    // 32-64 adaptation: in_bitforselect = in_address_field[2]

    // The width of in_bitforselect is 
    //  log2(OUT_NUM_SYMBOLS) - log2(IN_NUM_SYMBOLS) =
    //  log2(RATIO)
    
    // The msb of in_bitforselect is driven by
    //   in_adress_field[log2(OUT_NUMSYMBOLS) - 1]
    // The lsb of in_adress_field is driven by
    //   in_adress_field[log2(IN_NUMSYMBOLS)]


    // Generation of internal reset synchronization
    reg internal_sclr;
    generate if (SYNC_RESET == 1) begin : rst_syncronizer
       always @ (posedge clk) begin
          internal_sclr <= reset;
       end
    end
    endgenerate
 
    reg [clogb2(RATIO)-1:0] in_bitforselect;
    integer i, j;
   
    // ----------------------------------------
    // Input Field Mapping
    // ----------------------------------------
    reg [ADDRESS_W-1:0] address_for_adaptation;
    always @* begin
        in_size_field            = in_data[IN_PKT_BURST_SIZE_H :IN_PKT_BURST_SIZE_L ];
        in_data_field            = in_data[IN_PKT_DATA_H       :IN_PKT_DATA_L       ];
        in_byteen_field          = in_data[IN_PKT_BYTEEN_H     :IN_PKT_BYTEEN_L     ];
        address_from_packet      = in_data[IN_PKT_ADDR_H       :IN_PKT_ADDR_L       ];
        in_byte_cnt_field        = in_data[IN_PKT_BYTE_CNT_H   :IN_PKT_BYTE_CNT_L   ];
        in_cmpr_read             = in_data[IN_PKT_TRANS_COMPRESSED_READ];
        in_write                 = in_data[IN_PKT_TRANS_WRITE];
        in_lock_field            = in_data[IN_PKT_TRANS_EXCLUSIVE];
        in_burst_type_field      = in_data[IN_PKT_BURST_TYPE_H :IN_PKT_BURST_TYPE_L ];
        in_response_status_field = in_data[IN_PKT_RESPONSE_STATUS_H :IN_PKT_RESPONSE_STATUS_L];
        if (ROLE_BASED_USER) begin
           in_poison_field          = in_data[IN_PKT_POISON_H : IN_PKT_POISON_L ];
           in_datachk_field         = in_data[IN_PKT_DATACHK_H : IN_PKT_DATACHK_L]; 
           in_addrchk_field         = in_data[IN_PKT_ADDRCHK_H : IN_PKT_ADDRCHK_L];
           in_sai_field             = in_data[IN_PKT_SAI_H     : IN_PKT_SAI_L];       
           in_user_data_field       = in_data[IN_PKT_USER_DATA_H:IN_PKT_USER_DATA_L]; 
        end
    end

    // ----------------------------------------
    // Process unaligned address for first address of the burst
    // ----------------------------------------
    generate
    if (IN_NUMSYMBOLS > OUT_NUMSYMBOLS && ENABLE_ADDRESS_ALIGNMENT) begin
        reg [ADDRESS_W + (BWRAP_W-1) + BURST_SIZE_W + BURST_TYPE_W - 1 :0] address_for_alignment;
        reg [ADDRESS_W + clogb2(IN_NUMSYMBOLS)-1:0] address_after_aligned;

        assign address_for_alignment = {address_from_packet, in_size_field};
        assign address_for_adaptation = address_after_aligned[ADDRESS_W-1:0];
        
        altera_merlin_address_alignment
        #(
           .ADDR_W            (ADDRESS_W),
           .BURSTWRAP_W       (BWRAP_W),
           .INCREMENT_ADDRESS (0),
           .NUMSYMBOLS        (IN_NUMSYMBOLS),
           .SIZE_W            (BURST_SIZE_W),
           .SYNC_RESET        (SYNC_RESET)
        ) check_and_align_address_to_size
        (
           .clk       (clk),
           .reset     (reset),
           .in_data   (address_for_alignment),
           .out_data  (address_after_aligned),
           .in_valid  (),
           .in_sop    (),
           .in_eop    (),
           .out_ready ()
        );
    end else begin
        assign address_for_adaptation = address_from_packet;
    end
    endgenerate

    generate 
        if (FIRST_EXISTS) begin : gen_field
            always @* begin
                in_first_field = in_data[IN_FIRST_H:IN_FIRST_L];
            end
        end else begin
            always @* begin
                in_first_field = '0;
            end
        end
        if (MID_EXISTS) begin
            always @* begin
                in_mid_field = in_data[IN_MID_H:IN_MID_L];
            end
        end else begin
            always @* begin
                in_mid_field = '0;
            end
        end
        if (LAST_EXISTS) begin
            always @* begin
                in_last_field = in_data[IN_LAST_H:IN_LAST_L];
            end
        end
    endgenerate

    generate
      
      //-------------------------------------------------------
      //-------------------------------------------------------
      // Wide-to-Narrow
      //
      // For every input cycle, we drive out a bunch'o'output 
      // cycles.  Nothing fancier.  Yes, it could be more
      // optimal, but we'll leave that for another day.
      //-------------------------------------------------------
      //-------------------------------------------------------
      if (IN_NUMSYMBOLS > OUT_NUMSYMBOLS)  begin

         wire [31:0] cmd_burst_size = CONSTANT_BURST_SIZE ? IN_NUMSYMBOLS : bytes_in_transfer(in_size_field);
         
         // Below mess is just to avoid Quartus warnings about mis-sized assignments.
         wire [31:0] int_out_numsymbols = OUT_NUMSYMBOLS;
         wire [clogb2(OUT_NUMSYMBOLS):0] sized_out_numsymbols = int_out_numsymbols[clogb2(OUT_NUMSYMBOLS):0];

         wire [31:0] int_out_size = (cmd_burst_size < OUT_NUMSYMBOLS) ? cmd_burst_size : OUT_NUMSYMBOLS;
         wire [SIZE_W-1:0] sized_out_size = int_out_size[SIZE_W-1:0];

         wire [31:0] int_ratio_minus_1 = (cmd_burst_size / OUT_NUMSYMBOLS) - 1;
         wire [clogb2(RATIO)-1:0] sized_ratio_minus_1 = int_ratio_minus_1[clogb2(RATIO)-1:0];

         wire [31:0] int_log2_out_numsymbols = clogb2(OUT_NUMSYMBOLS);
         wire [BURST_SIZE_W-1:0] log2_out_numsymbols = int_log2_out_numsymbols[BURST_SIZE_W-1:0];

         wire [31:0] int_byte_cnt_factor = (in_size_field < log2_out_numsymbols) ? log2_out_numsymbols : in_size_field;
         wire [BURST_SIZE_W-1:0] sized_byte_cnt_factor = int_byte_cnt_factor[BURST_SIZE_W-1:0];

         reg single_response_expected;
         reg only_one_segment_asserted;
         reg [RATIO-1:0] segments_with_be_asserted;
         reg [clogb2(RATIO)-1:0] count;
         reg [POISON_W: 0 ] poison_reg;

         assign single_response_expected = (RESPONSE_PATH && ((only_one_segment_asserted && in_startofpacket && in_endofpacket) || in_write));      

         if(CONSTANT_BURST_SIZE == 1) begin 
            always @ (posedge clk) begin
               if(~use_reg) begin
                  data_reg     <= in_data_field[IN_DATA_W-1:OUT_NUMSYMBOLS*SYMBOL_W];
                  byteen_reg   <= in_byteen_field >> OUT_NUMSYMBOLS;
                  
                     user_data_reg     <= '0;

                  if(ADDRESS_W == WN_ADDR_SELECT)
                     address_reg[ADDRESS_W -1 : WN_ADDR_SELECT-1] <= in_address_field[ADDRESS_W -1 : WN_ADDR_SELECT-1];
                  else
                     address_reg[ADDRESS_W -1 : WN_ADDR_SELECT] <= in_address_field[ADDRESS_W -1 : WN_ADDR_SELECT];

                  address_reg[WN_ADDR_SELECT - 1 : 0]        <= sized_out_numsymbols;
                  byte_cnt_reg <= in_byte_cnt_field - sized_out_numsymbols;
                  
                  if(ROLE_BASED_USER)
                     datachk_reg <= in_datachk_field >> OUT_DATACHK_W ;
                  else
                     datachk_reg <= '0;
               end 
               else if(out_ready) begin  
                  // when data width ratio of W2N system is 2:1 , data_reg gets right shifted by it's width. To avoid 
                  // warning for this scenario, we directly clear data_reg.
                  if (IN_DATA_W == (2 * OUT_NUMSYMBOLS * SYMBOL_W))
                          data_reg     <= 'h0;
                  else 
                          data_reg     <= data_reg    >> (OUT_NUMSYMBOLS * SYMBOL_W);
        
                  byteen_reg   <= byteen_reg  >> (OUT_NUMSYMBOLS);

                  if(ADDRESS_W == WN_ADDR_SELECT)
                     address_reg[ADDRESS_W -1 : WN_ADDR_SELECT-1] <= in_address_field[ADDRESS_W -1 : WN_ADDR_SELECT-1];
                  else
                     address_reg[ADDRESS_W -1 : WN_ADDR_SELECT] <= in_address_field[ADDRESS_W -1 : WN_ADDR_SELECT];

                  address_reg[WN_ADDR_SELECT - 1 : 0]        <= address_reg[WN_ADDR_SELECT - 1 : 0] + sized_out_numsymbols;
                  byte_cnt_reg <= byte_cnt_reg - sized_out_numsymbols;
                  
                  if(ROLE_BASED_USER) begin
                      datachk_reg <= datachk_reg >> OUT_DATACHK_W ;
                          user_data_reg     <= '0;
                  end
                  else  begin
                  datachk_reg <= '0;
                  user_data_reg     <= '0;
                  end

               end
            end
         end    // end CONSTANT_BURST_SIZE = 1
         else begin
            always @ (posedge clk) begin
               if(~use_reg) begin
                  address_reg <= in_address_field + sized_out_size;
                  byte_cnt_reg <= (in_byte_cnt_field >> clogb2(IN_NUMSYMBOLS) << sized_byte_cnt_factor) - sized_out_numsymbols;
               end
               else if(out_ready) begin
                  address_reg <= address_reg + sized_out_size;
                  byte_cnt_reg <= byte_cnt_reg - sized_out_numsymbols;
               end
            end
         end   // end CONSTANT_BURST_SIZE = 0

         if (SYNC_RESET == 0)  begin :async_rst0
            always @(posedge clk, posedge reset) begin
               if (reset) begin
                  count        <= '0;
                  use_reg      <= '0;
                  endofpacket_reg <= '0;
               end else begin
                  // If we're not working on a wide datum, 
                  // then wait until one arrives.
                  if (~use_reg) begin
                     endofpacket_reg <= in_endofpacket;

                     if (in_valid && out_ready && !in_cmpr_read && (cmd_burst_size > OUT_NUMSYMBOLS) && !single_response_expected) begin
                        // Data has arrived!
                        count   <= sized_ratio_minus_1;
                        use_reg <= 1'b1;
                     end

                  end else begin // if (count == 0)
                     // We have a wide datum in progress.  Just wait until 
                     // the previous datum is taken, and then set 
                     // up the next transfer.
                     if (out_ready) begin
                        count <= count - 1'b1;
                        if (count == 1'b1)
                          // We're at the end of this word.
                          use_reg <= '0;

                     end // if (out_ready)
                  end // else: !if(count == 0)
               end // if (posedge clk)
            end // always @ (clk, reset)
         end // async_rst0
         else begin // sync_rst0
       
            always @(posedge clk) begin
               if (internal_sclr) begin
                  count        <= '0;
                  use_reg      <= '0;
                  endofpacket_reg <= '0;
               end else begin
                  // If we're not working on a wide datum, 
                  // then wait until one arrives.
                  if (~use_reg) begin
                     endofpacket_reg <= in_endofpacket;

                     if (in_valid && out_ready && !in_cmpr_read && (cmd_burst_size > OUT_NUMSYMBOLS) && !single_response_expected) begin
                        // Data has arrived!
                        count   <= sized_ratio_minus_1;
                        use_reg <= 1'b1;
                     end

                  end else begin // if (count == 0)
                     // We have a wide datum in progress.  Just wait until 
                     // the previous datum is taken, and then set 
                     // up the next transfer.
                     if (out_ready) begin
                        count <= count - 1'b1;
                        if (count == 1'b1)
                          // We're at the end of this word.
                          use_reg <= '0;

                     end // if (out_ready)
                  end // else: !if(count == 0)
               end // if (posedge clk)
            end // always @ (clk, reset)
          end // sync_rst0      

         always @* begin
            // Calculate in_ready.
            // If count is 0, then we don't have data underway, and we 
            // definitely won't be ready for it the first time 'round.
            // If count is '1', then we're finishing a set, and we're 
            //   ready if the output is.
            // If count > 1, then we're mid set, and certainly 
            //   not ready.
            in_ready = 0;
            if ( (cmd_burst_size <= OUT_NUMSYMBOLS) || count == 1 || in_cmpr_read )
               in_ready = out_ready;

            out_valid                 = in_valid;
            out_channel               = in_channel;
            out_startofpacket         = in_startofpacket;
            out_endofpacket           = 0;
                                      
            out_size_field            = (cmd_burst_size < OUT_NUMSYMBOLS) ? in_size_field : log2_out_numsymbols;
            if (CONSTANT_BURST_SIZE) begin // For Avalon only
                out_byteen_field   = in_byteen_field[OUT_NUMSYMBOLS-1:0];
                out_data_field     = in_data_field[OUT_NUMSYMBOLS * SYMBOL_W-1:0];
                out_byte_cnt_field = in_byte_cnt_field;
                if(ROLE_BASED_USER) begin
                   out_datachk_field  = in_datachk_field[OUT_DATACHK_W-1:0];
                        out_user_data_field     = '0;
                end
                else begin
                   out_datachk_field  = '0;
                   out_user_data_field     = '0;
                end

            end else begin
                out_byte_cnt_field = in_byte_cnt_field >> clogb2(IN_NUMSYMBOLS) << sized_byte_cnt_factor;
            end
            if(ROLE_BASED_USER) 
               out_addrchk_field   = in_addrchk_field[OUT_ADDRCHK_W-1:0];   
            else 
               out_addrchk_field   = '0;

            out_first_field           = in_first_field;
            out_mid_field             = in_mid_field;
            out_last_field            = in_last_field;
            out_cmpr_read             = in_cmpr_read;
            out_lock_field            = in_lock_field;
            out_burst_type_field      = in_burst_type_field;
            out_response_status_field = in_response_status_field;

            // Case when command size <= OUT_NUMSYMBOLS: pass the cycle
            // through, unmodified
            if (cmd_burst_size <= OUT_NUMSYMBOLS) begin
                out_endofpacket = in_endofpacket;
                in_address_field = address_from_packet;
            end // (cmd_burst_size <= OUT_NUMSYMBOLS)
            else begin 
                // Case when we need to bus size data (size > OUT_NUMSYMBOLS). 
                out_lock_field     = 0;
                // Change fixed burst type opcodes to the repeated wrap
                // opcode.
                if (in_burst_type_field == 2'b00) begin
                    out_burst_type_field = 2'b11;
                end
                // On the first address of the burst, align and send this 
                // address to the network
                in_address_field = address_for_adaptation;
            end // (cmd_burst_size > OUT_NUMSYMBOLS)

            out_address_field         = in_address_field;
            int_output_sel            = in_address_field >> log2_out_numsymbols ;
            if (in_cmpr_read)
                out_endofpacket = 1;
            
            if (use_reg) begin
               out_startofpacket = 0;
               // If it's the last cycle, or if there's no more data, 
               // we can allow an endofpacket.
               if (count == 1) 
                  out_endofpacket = endofpacket_reg;
               
               out_byte_cnt_field = byte_cnt_reg;
               out_address_field  = address_reg;
               if (CONSTANT_BURST_SIZE) begin // Avalon system
                   out_data_field     = data_reg[(OUT_NUMSYMBOLS * SYMBOL_W)-1:0];
                   out_byteen_field   = byteen_reg[OUT_NUMSYMBOLS-1:0];
                   if(ROLE_BASED_USER) begin
                       out_datachk_field  = datachk_reg[OUT_DATACHK_W-1:0];
                           out_user_data_field  = user_data_reg[OUT_USER_DATA_W-1:0];
                   end
                   else begin 
                       out_datachk_field    = '0;
                       out_user_data_field  = '0;
                   end
               end
               int_output_sel     = address_reg >> log2_out_numsymbols;
            end
 
            output_sel                = int_output_sel[WN_ADDR_LSBS-1:0];
            if (!CONSTANT_BURST_SIZE) begin
                out_byteen_field       = byteen_array[output_sel];
                out_data_field         = data_array[output_sel];
                if(ROLE_BASED_USER) begin
                    out_datachk_field  = datachk_array[output_sel];
                         out_user_data_field = '0;
                end
                else begin 
                    out_datachk_field   = '0;
                    out_user_data_field = '0;
                end
            end
            
            // Check each output-sized segment to see whether it 
            // is enabled (byteenables)
            segments_with_be_asserted = 0;
            for (i = 0; i < RATIO; i=i+1) begin
                segments_with_be_asserted[i] = |in_byteen_field[i*OUT_BYTEEN_W +: OUT_BYTEEN_W];
            end

            // Determine whether only one segment is asserted. This code detects a power of two,
            // i.e. only 1 bit is asserted.
            only_one_segment_asserted = (segments_with_be_asserted && !(segments_with_be_asserted & (segments_with_be_asserted - 1))); 

            //-----------------------------------------
            // Optimization for non-bursting wide-narrow response.
            //
            // Only one segment of the wide word will have asserted
            // byteenables. Just pass that segment through and drop
            // the rest. This should synthesize to an and-or mux.
            //-----------------------------------------
            if (OPTIMIZE_FOR_RSP | single_response_expected) begin
                out_startofpacket  = in_startofpacket;
                out_endofpacket    = in_endofpacket;
                in_ready           = out_ready;
                //-----------------------------------------
                // Not correct, but nothing in the response path looks
                // at these today (10.1). Must be corrected when we allow
                // multiple width adapters on a path.
                //-----------------------------------------
                out_address_field  = in_address_field;
                out_byte_cnt_field = in_byte_cnt_field;

                out_data_field   = '0;
                out_byteen_field = '0;
                if(ROLE_BASED_USER)
                    out_datachk_field = '0;//AXI5Lite

                for (i = 0; i < RATIO; i=i+1) begin
                    mask = '0;
                    for (j = 0; j < OUT_NUMSYMBOLS; j=j+1) begin
                        mask |= {SYMBOL_W{in_byteen_field[i*OUT_NUMSYMBOLS+j]}} << (j*SYMBOL_W);
                    end
                    if(ROLE_BASED_USER) begin
                        user_data_mask ='0; 
                        for (j = 0; j < OUT_NUMSYMBOLS; j=j+1) begin
                            user_data_mask |= {USER_DATA_SYMBOL_W{in_byteen_field[i*OUT_NUMSYMBOLS+j]}} << (j*USER_DATA_SYMBOL_W);
                        end
                    end 
                    else 
                    begin
                    user_data_mask = '0;
                    end

                    out_data_field |= mask & in_data_field[i*OUT_SEGMENT_W +: OUT_SEGMENT_W];
                    out_byteen_field |= in_byteen_field[i*OUT_NUMSYMBOLS +: OUT_NUMSYMBOLS];
                    //AXI5Lite
                    if(ROLE_BASED_USER) begin
                    out_datachk_field |= in_byteen_field[i*OUT_NUMSYMBOLS +: OUT_NUMSYMBOLS] & in_datachk_field[i*OUT_NUMSYMBOLS +: OUT_NUMSYMBOLS];
                            out_user_data_field = '0;
                    end
                    else begin
                    out_datachk_field = '0;
                    out_user_data_field = '0;
                    end
                end
            end
            else begin  // to prevent latches
                j = 0;
                mask = '0;
            end

         end // always @ *
                  
         //-------------------------------------------------------
         // Configuration Error Checking
         //-------------------------------------------------------
         // synthesis translate_off
         initial begin
            if (RATIO * OUT_NUMSYMBOLS != IN_NUMSYMBOLS) begin
               $display("%m : The ratio of input symbols to output symbols must be an integer.");
               $stop();
            end
         end
         // synthesis translate_on
         if (!CONSTANT_BURST_SIZE) begin
             integer ibyte;
             always @* begin
                 for(ibyte=0; ibyte<RATIO; ibyte=ibyte+1) begin: mux_mapping
                     data_array[ibyte] = in_data_field[(ibyte*OUT_NUMSYMBOLS*SYMBOL_W)+:OUT_NUMSYMBOLS*SYMBOL_W];
                     byteen_array[ibyte] = in_byteen_field[(ibyte*OUT_NUMSYMBOLS)+:OUT_NUMSYMBOLS];
                     //AXI5Lite
                     if(ROLE_BASED_USER) begin
                     datachk_array[ibyte] = in_datachk_field[(ibyte*OUT_DATACHK_W)+:OUT_DATACHK_W];
                             user_data_array[ibyte] = '0;
                     end
                     else begin
                     datachk_array[ibyte] = '0;
                     user_data_array[ibyte] = '0;
                     end
                 end
             end
         end
         
        if(ROLE_BASED_USER) begin
        //AXI5Lite poison logic
        // when IN_DATA is greater then 64 shifting operation exists otherwise in poison width = Out poison width
        if((IN_DATA_W > 64 ) && (OUT_DATA_W >= 64)) begin  
            always @(posedge clk) begin
                if (~use_reg) begin
                     poison_reg <= in_poison_field[OUT_POISON_W+:(IN_POISON_W-OUT_POISON_W)] ;  
                end else if (out_ready) begin
                     poison_reg <= poison_reg >> OUT_POISON_W ;
                end 
            end
            always @(*) begin
                if (use_reg)begin
                    out_poison_field = poison_reg[OUT_POISON_W-1: 0];
                end else begin 
                    out_poison_field = in_poison_field[OUT_POISON_W-1 : 0 ];
                end 
            end              
        end  
        else if(IN_DATA_W > 64 && OUT_DATA_W < 64)begin
           localparam POISON_REPL = 64/OUT_DATA_W;
           reg [(IN_POISON_W*POISON_REPL)-1:0] poison_bits_replicated;
           reg [(IN_POISON_W*POISON_REPL - OUT_POISON_W )-1:0]poison_shift_reg;

            function reg[(IN_POISON_W*POISON_REPL)-1:0]bits_replication;
              input reg [IN_POISON_W-1:0] in_poison_field;   
                for (int i = 0; i<IN_POISON_W; i++) begin
                  for (int j = 0; j<POISON_REPL; j++)begin
                    bits_replication [i*POISON_REPL+j] = in_poison_field[i];
                  end 
                end  
            endfunction
             
            assign poison_bits_replicated = bits_replication(in_poison_field);           
            always @(posedge clk) begin
              if (~use_reg) begin
                poison_shift_reg <= poison_bits_replicated[(IN_POISON_W*POISON_REPL)-1:OUT_POISON_W];  
              end else if (out_ready) begin
                poison_shift_reg <= poison_shift_reg >> OUT_POISON_W; 
              end   
            end   
       
            always @(*) begin
               if (use_reg)begin
                   out_poison_field  = poison_shift_reg[OUT_POISON_W-1:0];
               end 
               else begin 
                   out_poison_field  = in_poison_field[OUT_POISON_W-1:0];
               end 
            end
        end    
        else begin 
            always @(*) begin
                 out_poison_field = in_poison_field; // this case when OUT_POISON and IN_POISON is of 1 bit
            end 
        end

       always @(posedge clk) begin
          if(reset)
            sai_reg <= '0;
          else if (out_startofpacket && out_valid  && out_ready )
            sai_reg <= in_sai_field[OUT_SAI_W-1:0];
       end

       always @(*) begin
          if(ROLE_BASED_USER) begin
              if(out_startofpacket && out_valid  && out_ready )
                  out_sai_field = in_sai_field[OUT_SAI_W-1:0] ;
              else if(~out_startofpacket && out_valid  && out_ready)
                  out_sai_field = sai_reg;
              else 
                  out_sai_field = sai_reg;
          end else
              out_sai_field = '0;
       end                 
  
      end
      end // if (IN_NUMSYMBOLS > OUT_NUMSYMBOLS)
        
      //-------------------------------------------------------
      //-------------------------------------------------------
      // Narrow-to-Wide
      //-------------------------------------------------------
      //-------------------------------------------------------
      if (OUT_NUMSYMBOLS > IN_NUMSYMBOLS)  begin
         localparam WIDE_POISON = (OUT_POISON_W-IN_POISON_W)+1;
         wire                    p0_valid;
         reg                     p0_startofpacket;
         reg                     p0_endofpacket;
         reg [IN_DATA_W-1:0]     p0_data_field; 
         reg [IN_POISON_W-1:0]   p0_poison_field; //AXI5Lite        
         reg [IN_BYTEEN_W-1:0]   p0_byteen_field;
         reg [IN_DATACHK_W-1:0]  p0_datachk_field;//AXI5Lite
         reg [IN_USER_DATA_W-1:0]p0_user_data_field; 
         reg [ADDRESS_W-1:0]     p0_address_field;
         reg [BWRAP_W-1:0]       p0_bwrap_field;
         reg [BYTE_CNT_W-1:0]    p0_byte_cnt_field;
         reg [clogb2(RATIO)-1:0] p0_bitforselect;
         reg                     p0_cmpr_read;
         reg [FIRST_W-1:0]       p0_first_field;
         reg [MID_W-1:0]         p0_mid_field;
         reg [LAST_W-1:0]        p0_last_field;
         reg                     p0_use_reg;
         reg [ST_CHANNEL_W-1:0]  p0_channel;
         reg [BURST_SIZE_W-1:0]  p0_burst_size;
         reg [BURST_SIZE_W-1:0]  p0_ori_burst_size;
         reg                     p0_out_lock_field;
         reg [BURST_TYPE_W-1:0]  p0_burst_type_field;
         
         reg [RESPONSE_STATUS_W-1:0] p0_response_status_field;
         reg                     p0_reg_startofpacket;
         reg                     p0_reg_endofpacket;
         reg [IN_DATA_W-1:0]     p0_reg_data_field; 
         reg [IN_POISON_W-1:0]   p0_reg_poison_field; //AXI5Lite
         reg [IN_BYTEEN_W-1:0]   p0_reg_byteen_field;
         reg [IN_DATACHK_W-1:0]  p0_reg_datachk_field; //AXI5Lite
         reg [ADDRESS_W-1:0]     p0_reg_address_field;
         reg [BWRAP_W-1:0]       p0_reg_bwrap_field;
         reg [BYTE_CNT_W-1:0]    p0_reg_byte_cnt_field;
         reg [clogb2(RATIO)-1:0] p0_reg_bitforselect;
         reg                     p0_reg_cmpr_read;
         reg [FIRST_W-1:0]       p0_reg_first_field;
         reg [MID_W-1:0]         p0_reg_mid_field;
         reg [LAST_W-1:0]        p0_reg_last_field;
         reg [ST_CHANNEL_W-1:0]  p0_reg_channel;
         reg [BURST_SIZE_W-1:0]  p0_reg_burst_size;
         reg [BURST_SIZE_W-1:0]  p0_reg_ori_burst_size;
         reg [BURST_TYPE_W-1:0]  p0_reg_burst_type_field;
         reg [RESPONSE_STATUS_W-1:0] p0_reg_response_status_field;
         reg                     p0_reg_out_lock_field;
         wire                    p1_valid;
         reg                     p1_ready;
         reg                     p1_startofpacket;
         reg                     p1_endofpacket;
         reg [IN_DATA_W-1:0]     p1_data_field; 
         reg [IN_POISON_W-1:0]   p1_poison_field;
         reg [IN_BYTEEN_W-1:0]   p1_byteen_field;
         reg [IN_DATACHK_W-1:0]  p1_datachk_field; //AXI5Lite
         reg [ADDRESS_W-1:0]     p1_address_field;
         reg [ADDRESS_W-1:0]     out_address_field_mask;
         reg [BYTE_CNT_W-1:0]    p1_byte_cnt_field;
         reg [IN_USER_DATA_W-1:0]p1_user_data_field;
         
         reg [BURST_SIZE_W-1:0]  p1_burst_size;
         reg [BYTE_CNT_W-1:0]    p1_byte_cnt_unpack_field;
         wire                    response_data_packing;
         reg [clogb2(RATIO)-1:0] p1_shift_correct_ouput_segments;
         reg [clogb2(RATIO)-1:0] p1_push_data_to_output;
         
         reg                     p1_cmpr_read;
         reg [RESPONSE_STATUS_W-1:0] p1_response_status_field;
         reg                     unc_sink_valid;
         wire                    unc_sink_ready;
         wire                    unc_src_startofpacket;
         wire                    unc_src_endofpacket;
         wire                    unc_src_valid;
         wire [ADDRESS_W-1:0]    unc_src_addr;
         wire [BYTE_CNT_W-1:0]   unc_src_byte_cnt;

         wire                    aligned_addr;
         wire                    aligned_byte_cnt;
         wire                    unaligned_read;

         reg [BYTE_CNT_W-1:WN_ADDR_SELECT] count;
         reg                               count_eq_zero;

         wire [31:0]             int_in_numsymbols             = IN_NUMSYMBOLS;
         wire [BYTE_CNT_W-1:0]   byte_cnt_sized_in_num_symbols = int_in_numsymbols[BYTE_CNT_W-1:0];
         reg  [9:0]              cmd_burst_size;
         wire [31:0]             out_numsymbols_wire           = LOG_OUT_NUMSYMBOLS;
         wire [31:0]             int_encoded_burstsize         = NW_BITFORSELECT_R; //NW_BITFORSELECT_R is the log2 of IN_NUMSYMBOLS
         wire [BURST_SIZE_W-1:0] encoded_burstsize             = int_encoded_burstsize[BURST_SIZE_W-1:0];     
         reg  [WIDE_POISON-1:0]  poison_reg                    = '0;         
            
        // Care about burstwrap on command path only
        if (RESPONSE_PATH == 0) begin
            assign in_burstwrap_field = in_data[IN_PKT_BURSTWRAP_H:IN_PKT_BURSTWRAP_L];
        end else begin
            assign in_burstwrap_field = {BWRAP_W{1'b1}};
        end   

        // To use "read response merging" the Width adapter need to know the size of the command
        // to check if downside happen. For AXI system, the fifo will store this number (non-packing: we use "combined width adapter")
        // but in case system without AXI, the system use stand alone width adapter and it cannot read this value
        // Make a condition incase we see stand alone WA, set this in_command_burst_size to input size
        //wire [2:0] in_command_burst_size = out_numsymbols_wire[2:0];
        //if (!((PACKING == 1) & (CONSTANT_BURST_SIZE == 1))) // stand alone WA
        //begin
        //assign in_command_burst_size = in_command_size_data;
        //end
        reg [BURST_SIZE_W-1:0]  in_ori_size_field;
        always @* begin
            in_ori_size_field = in_data[IN_PKT_ORI_BURST_SIZE_H :IN_PKT_ORI_BURST_SIZE_L ];
        end
        
        reg [9:0]   size_ratio;

         always @ (posedge clk) begin
            if(unaligned_read) begin
               p0_reg_address_field  <= p0_address_field; 
               p0_reg_data_field     <= p0_data_field;    
            end
         end


         // --------------------------------------------
         // Stage 0: buffer the input cycle if read burst 
         // uncompression is going to happen.
         //
         // This avoids the possibility of a master receiving a premature
         // response while its read burst is still being waitrequested.
         // --------------------------------------------
        if (SYNC_RESET == 0) begin : async_rst1
           always @(posedge clk, posedge reset) begin
              if (reset) begin
                  p0_use_reg            <= 1'b0;
              end else begin
                  if (unaligned_read & in_valid)
                     p0_use_reg <= 1'b1;
                  if (unc_src_endofpacket & p1_ready)
                     p0_use_reg <= 1'b0;
               end
            end
        end // async_rst1
        else begin // sync_rst1
           always @(posedge clk) begin
               if (internal_sclr) begin
                  p0_use_reg            <= 1'b0;
               end else begin
                  if (unaligned_read & in_valid)
                     p0_use_reg <= 1'b1;
                  if (unc_src_endofpacket & p1_ready)
                     p0_use_reg <= 1'b0;
               end
           end
        end // sync_rst1
     
        always @(posedge clk) begin
               p0_reg_startofpacket  <= p0_startofpacket;
               p0_reg_endofpacket    <= p0_endofpacket;   
               p0_reg_bwrap_field    <= p0_bwrap_field;
               p0_reg_byteen_field   <= p0_byteen_field; 
               if(ROLE_BASED_USER)
               p0_reg_datachk_field  <= p0_datachk_field; //AXI5Lite
               else
               p0_reg_datachk_field  <= 0; //AXI5Lite
               p0_reg_byte_cnt_field <= p0_byte_cnt_field;
               p0_reg_cmpr_read      <= p0_cmpr_read;     
               p0_reg_first_field    <= p0_first_field;   
               p0_reg_mid_field      <= p0_mid_field;     
               p0_reg_last_field     <= p0_last_field;    
               p0_reg_channel        <= p0_channel;
               p0_reg_burst_size     <= p0_burst_size;
               p0_reg_ori_burst_size <= p0_ori_burst_size;
               p0_reg_out_lock_field <= p0_out_lock_field;
               p0_reg_burst_type_field       <= p0_burst_type_field;
               p0_reg_response_status_field  <= p0_response_status_field;
               if(ROLE_BASED_USER)
               p0_reg_poison_field           <= p0_poison_field; //AXI5Lite
               else
               p0_reg_poison_field           <= '0; //AXI5Lite
        end

        always @* begin
            in_ready = p1_ready;
            // accept on the first cycle 
            if (p0_use_reg)
                in_ready = '0;
            else if (unaligned_read & in_valid)
                in_ready = 1;
        end
         
        always @* begin
              if(OUT_SAI_W > IN_SAI_W) 
                 out_sai_field = {{(OUT_SAI_W-IN_SAI_W){1'b0}},in_sai_field};
              else
                 out_sai_field = in_sai_field[OUT_SAI_W-1:0];
                 
              if (OUT_ADDRCHK_W > IN_ADDRCHK_W )
                  out_addrchk_field = {{(OUT_ADDRCHK_W-IN_ADDRCHK_W){1'b0}},in_addrchk_field};          
              else
                 out_addrchk_field = in_addrchk_field[OUT_ADDRCHK_W-1:0];
        end                 
         

        always @* begin
            p0_startofpacket  = in_startofpacket;
            p0_endofpacket    = in_endofpacket;
            p0_data_field     = in_data_field;  
            p0_bwrap_field    = in_burstwrap_field;
            p0_byteen_field   = in_byteen_field;
            p0_address_field  = address_for_adaptation;  // read address from oacket
            if (ROLE_BASED_USER)  begin
              p0_poison_field   = in_poison_field; //AXI5Lite            
              p0_datachk_field  = in_datachk_field; //AXI5Lite
              if(BITSPERBYTE)
                 p0_user_data_field  = in_user_data_field;  
              else 
                 p0_user_data_field  = '0;  
            end
            else begin
              p0_poison_field   = '0;
              p0_datachk_field  = '0;
              p0_user_data_field= '0;  
            end
            p0_byte_cnt_field = in_byte_cnt_field;
            p0_cmpr_read      = in_cmpr_read;     
            p0_first_field    = in_first_field;   
            p0_mid_field      = in_mid_field;     
            p0_last_field     = in_last_field;
            p0_channel        = in_channel;
            p0_burst_size     = in_size_field;
            p0_ori_burst_size = in_ori_size_field;
            p0_out_lock_field = in_lock_field;
            p0_burst_type_field         = in_burst_type_field;
            p0_response_status_field    = in_response_status_field;
            if (p0_use_reg) begin
               p0_startofpacket  = p0_reg_startofpacket;
               p0_endofpacket    = p0_reg_endofpacket;
               p0_bwrap_field    = p0_reg_bwrap_field;
               p0_byteen_field   = p0_reg_byteen_field;
               p0_address_field  = p0_reg_address_field;  
               p0_byte_cnt_field = p0_reg_byte_cnt_field;
               p0_cmpr_read      = p0_reg_cmpr_read;     
               p0_first_field    = p0_reg_first_field;   
               p0_mid_field      = p0_reg_mid_field;     
               p0_last_field     = p0_reg_last_field;
               p0_channel        = p0_reg_channel;
               p0_burst_size     = p0_reg_burst_size;
               p0_ori_burst_size = p0_reg_ori_burst_size;
               p0_out_lock_field = p0_reg_out_lock_field;
               p0_burst_type_field      = p0_reg_burst_type_field;
               if (ROLE_BASED_USER) begin
                  p0_datachk_field  = p0_reg_datachk_field;//AXI5Lite
                  p0_poison_field   = p0_reg_poison_field;
                  if(BITSPERBYTE)
                     p0_user_data_field  = in_user_data_field;  
                  else 
                     p0_user_data_field  = '0;  
               end else begin
                  p0_datachk_field    = '0;
                  p0_poison_field     = '0;
                  p0_user_data_field  = '0;  
               end
            end
        end

        assign p0_valid = in_valid | p0_use_reg;

        // --------------------------------------------
        // Stage 1: uncompress the input packet if necessary
        // --------------------------------------------
        assign p1_valid = (unaligned_read) ? unc_src_valid : p0_valid;
        assign aligned_addr     = (p0_address_field[ALIGNED_BITS_L:0] == 0);
        assign aligned_byte_cnt = (p0_byte_cnt_field[ALIGNED_BITS_L:0] == 0);
        if ((RESPONSE_PATH == 0) && (PACKING == 1)) begin // if this is avalon then checking on aligned,
           assign unaligned_read   = p0_cmpr_read & (~aligned_addr || ~aligned_byte_cnt);
        end else begin
           assign unaligned_read   = '0;
        end
         
        always @* begin
           p1_data_field     = p0_data_field;
           if (ROLE_BASED_USER)
              p1_poison_field   = p0_poison_field; //AXI5Lite
           else 
              p1_poison_field   = '0; 
           p1_byteen_field   = p0_byteen_field;
           p1_startofpacket  = p0_startofpacket;
           p1_endofpacket    = p0_endofpacket;
           p1_address_field  = p0_address_field;
           p1_byte_cnt_field = p0_byte_cnt_field;
           if (ROLE_BASED_USER) begin 
              p1_datachk_field  = p0_datachk_field; //AXI5Lite
              if(BITSPERBYTE)
                 p1_user_data_field  = p0_user_data_field;  
              else 
                 p1_user_data_field  = '0;  
           end
           else begin 
              p1_datachk_field    = '0;
              p1_user_data_field  = '0;  
           end
           p1_cmpr_read      = p0_cmpr_read;
           p1_response_status_field    = p0_response_status_field;
           p1_burst_size     = p0_burst_size;
           unc_sink_valid    = 0;

           if (unaligned_read) begin
              unc_sink_valid    = p0_valid;
              p1_startofpacket  = unc_src_startofpacket;
              p1_endofpacket    = unc_src_endofpacket;
              p1_address_field  = unc_src_addr;
              p1_byte_cnt_field = unc_src_byte_cnt;
              p1_cmpr_read      = 0;
           end
        end

        altera_merlin_burst_uncompressor
        #(
            .ADDR_W      (ADDRESS_W),
            .BURSTWRAP_W (BWRAP_W),
            .BYTE_CNT_W  (BYTE_CNT_W),
            .PKT_SYMBOLS (IN_NUMSYMBOLS),
            .BURST_SIZE_W(BURST_SIZE_W),
            .SYNC_RESET  (SYNC_RESET)
        ) uncompressor (
            .clk                  (clk),
            .reset                (reset),

            .sink_startofpacket   (p0_startofpacket),
            .sink_endofpacket     (p0_endofpacket),
            .sink_valid           (unc_sink_valid),
            .sink_ready           (unc_sink_ready),
            .sink_addr            (p0_address_field),
            .sink_burstwrap       (p0_bwrap_field),
            .sink_byte_cnt        (p0_byte_cnt_field),
            .sink_is_compressed   (1'b1),   // should always be compressed
            .sink_burstsize       (encoded_burstsize),

            .source_startofpacket (unc_src_startofpacket),
            .source_endofpacket   (unc_src_endofpacket),
            .source_valid         (unc_src_valid),
            .source_ready         (p1_ready),
            .source_addr          (unc_src_addr),
            .source_burstwrap     (),
            .source_byte_cnt      (unc_src_byte_cnt),
            .source_is_compressed (),
            .source_burstsize     ()
        );

         // --------------------------------------------
         // Stage 2: perform narrow to wide adaptation on the beats
         // --------------------------------------------
         
         always @ (posedge clk) begin
            if (p0_valid && (out_ready || ~out_valid)) begin
               data_reg <= out_data_field[WIDE_DATA-1:0];
            end
         end

         always @ (posedge clk) begin
            if(p1_valid && (out_ready || ~out_valid)) begin
               if(p1_endofpacket || (p1_push_data_to_output == '1)) begin
                  byteen_reg <= '0;
                  datachk_reg <= '0;
                  poison_reg  <= '0;
               end else begin
                  byteen_reg <= out_byteen_field;
                  if (ROLE_BASED_USER) begin
                     datachk_reg <= out_datachk_field;
                     poison_reg  <= out_poison_field;
                     if(BITSPERBYTE) 
                         user_data_reg <= out_user_data_field;
                     else 
                         user_data_reg <= '0;
                  end else begin
                     datachk_reg   <= '0; 
                     poison_reg    <= '0; 
                     user_data_reg <= '0;
                  end
               end
            end else if (count_eq_zero == 1'b1) begin
               byteen_reg    <= '0;
               datachk_reg   <= '0;
               poison_reg    <= '0;
               user_data_reg <= '0;
            end
         end

         always @ (posedge clk) begin
            if (p1_valid && (out_ready || ~out_valid)) begin
               if (count_eq_zero) begin
                  if (~p1_endofpacket) begin
                     count <= p1_byte_cnt_field[BYTE_CNT_W-1:WN_ADDR_SELECT] - byte_cnt_sized_in_num_symbols[BYTE_CNT_W-1:WN_ADDR_SELECT];
                  end 
               end else begin
                  count <= count - byte_cnt_sized_in_num_symbols[BYTE_CNT_W-1:WN_ADDR_SELECT];
               end
            end
         end

         if (SYNC_RESET == 0) begin : async_rst2
            always @(posedge clk, posedge reset) begin
               if (reset) begin
                  startofpacket_reg <= '0;
                  count_eq_zero     <= '1;
                  response_status_reg <= '0;
               end else begin
                  
                  if (p1_valid && (out_ready || ~out_valid)) begin
                     // Lay input data & input byte enables into 
                     // the temp registers
                     response_status_reg   <= out_response_status_field;
                     // Capture the stuff that's to be held constant
                     if (count_eq_zero) begin
                        startofpacket_reg <= p1_startofpacket;
                        if (~p1_endofpacket) begin
                           count_eq_zero <=
                             ~|(p1_byte_cnt_field[BYTE_CNT_W-1:WN_ADDR_SELECT] - byte_cnt_sized_in_num_symbols[BYTE_CNT_W-1:WN_ADDR_SELECT]);
                        end 
                     end else begin
                        count_eq_zero <= ~|(count - byte_cnt_sized_in_num_symbols[BYTE_CNT_W-1:WN_ADDR_SELECT]);
                     end

                     //if (p1_endofpacket || (p1_shift_correct_ouput_segments == '1)) begin
                     if (p1_endofpacket || (p1_push_data_to_output == '1)) begin
                        response_status_reg <= '0;
                     end
                     
                     if (out_valid && out_ready) begin
                        startofpacket_reg <= '0;
                     end
                     
                  end // if (p1_valid && (out_ready || ~out_valid))
               end // if (posedge clk)
            end // always @ (clk, reset)
         end // async_rst2

         else begin // sync_rst2
            always @(posedge clk) begin
               if (internal_sclr) begin
                  startofpacket_reg <= '0;
                  count_eq_zero     <= '1;
                  response_status_reg <= '0;
               end else begin
                  
                  if (p1_valid && (out_ready || ~out_valid)) begin
                     // Lay input data & input byte enables into 
                     // the temp registers
                     response_status_reg   <= out_response_status_field;
                     // Capture the stuff that's to be held constant
                     if (count_eq_zero) begin
                        startofpacket_reg <= p1_startofpacket;
                        if (~p1_endofpacket) begin
                           count_eq_zero <=
                             ~|(p1_byte_cnt_field[BYTE_CNT_W-1:WN_ADDR_SELECT] - byte_cnt_sized_in_num_symbols[BYTE_CNT_W-1:WN_ADDR_SELECT]);
                        end 
                     end else begin
                        count_eq_zero <= ~|(count - byte_cnt_sized_in_num_symbols[BYTE_CNT_W-1:WN_ADDR_SELECT]);
                     end

                     //if (p1_endofpacket || (p1_shift_correct_ouput_segments == '1)) begin
                     if (p1_endofpacket || (p1_push_data_to_output == '1)) begin
                        response_status_reg <= '0;
                     end
                     
                     if (out_valid && out_ready) begin
                        startofpacket_reg <= '0;
                     end
                     
                  end // if (p1_valid && (out_ready || ~out_valid))
               end // if (posedge clk)
            end // always @ (clk, reset)
         end // sync_rst2

         always @* begin
            // Handle narrow-size transaction from the master: 
            // The width of in_bitforselect is 
            //  log2(OUT_NUM_SYMBOLS) - log2(IN_NUM_SYMBOLS) =
            //  log2(RATIO)
            // The msb of in_bitforselect is driven by: in_adress_field[log2(OUT_NUMSYMBOLS) - 1]
            // The lsb of in_adress_field is driven by: in_adress_field[log2(IN_NUMSYMBOLS)]

            // The function: mask_to_select_segments_for_size: is used to build a mask that changed at run-time
            // when narrow-size transaction, It recaculates the width of in_bitforselect base on size ratio

            // EX: Full-size transaction (2 bytes)N-W: in_bitforselect  = in_address[1:0]
            //     Narrow-size transaction(1 byte)N-W: in_bitforselect  = {1, in_address[0]}
            
            p1_shift_correct_ouput_segments = p1_address_field[NW_BITFORSELECT_L:NW_BITFORSELECT_R];
            
            // size ratio betwen command size and response size
            //cmd_burst_size = bytes_in_transfer(in_command_burst_size);
                   cmd_burst_size = bytes_in_transfer(p0_ori_burst_size);

            size_ratio = cmd_burst_size >> in_size_field; 
            
            if (RESPONSE_PATH == 0) begin 
            // if the WA is on command path, Avalon interconnect default
            // bitselectfor data packing and push out data are same, compile time 
                p1_push_data_to_output = p1_shift_correct_ouput_segments;
            end else begin 
            // the WA is on reponse path and default: PACKING = 1
            // on response path, need based on size, run-time, to determinite output segment
                p1_push_data_to_output = mask_to_select_correct_segments_for_size(p1_shift_correct_ouput_segments, size_ratio, clogb2(RATIO));
                out_address_field_mask = choose_packed_address_base_on_size(size_ratio, clogb2(RATIO));
            end

            // We push data to the output whenever the input is 
            // an endofpacket, or the input drives the most-significant
            // segment of the wider output word.
            out_valid = 0;
            if (PACKING == 1) begin
                if (p1_endofpacket || (p1_push_data_to_output == '1)) begin
                    out_valid = p1_valid;
                end
            end else begin
                out_valid = p1_valid;
            end

            out_startofpacket = p1_startofpacket || startofpacket_reg;
            out_endofpacket   = p1_endofpacket;

            // Compressed read with byte_cnt > input interface width: 
            // this is a read burst spanning more than the originating
            // interface of data, so all byteenables must be asserted.
            if (p1_cmpr_read && (p1_byte_cnt_field > IN_NUMSYMBOLS)) begin
                out_byteen_field = '1;
                if (ROLE_BASED_USER) begin
                    out_datachk_field = '1;
                end else begin
                    out_datachk_field = '0;
                end
            end else begin
                if (PACKING == 1) begin  // byteenable only affect on command path
                    out_byteen_field = byteen_reg;
                    out_byteen_field[p1_shift_correct_ouput_segments*IN_NUMSYMBOLS +: IN_NUMSYMBOLS] = p1_byteen_field;
                    if (ROLE_BASED_USER) begin
                        out_datachk_field = datachk_reg;
                        out_datachk_field[p1_shift_correct_ouput_segments*IN_NUMSYMBOLS +: IN_NUMSYMBOLS] = p1_datachk_field; 
                    end else begin
                        out_datachk_field = '0;
                    end
                end else begin // non-packing: shift input byteenable to correct position
                    out_byteen_field = (p1_byteen_field << (p1_shift_correct_ouput_segments*IN_NUMSYMBOLS));
                    if (ROLE_BASED_USER)
                        out_datachk_field = (p1_datachk_field << (p1_shift_correct_ouput_segments*IN_NUMSYMBOLS));
                    else
                        out_datachk_field = '0;
                end
            end
            
            // caculate bytecnt "unpack" according to OUTNUMSYMBOLS
            p1_byte_cnt_unpack_field = p1_byte_cnt_field << clogb2(RATIO);
            out_address_field = p1_address_field;

            if (RESPONSE_PATH == 0) begin
                if (PACKING == 1) begin // if the WA is on command path, Avalon interconnect default
                    out_data_field      = data_reg;
                    out_data_field[p1_shift_correct_ouput_segments*IN_DATA_W +: IN_DATA_W] = p1_data_field;
                        out_poison_field    = '0; 
                    out_byte_cnt_field  = quantized_byte_cnt_field;
                    out_address_field[NW_BITFORSELECT_L:0] = 0;
                    out_size_field      = out_numsymbols_wire[BURST_SIZE_W-1:0]; // for Avalon the size is converted to slave side
                        out_user_data_field      = '0;
                 end else begin
                    out_data_field      = (p1_data_field << (p1_shift_correct_ouput_segments *IN_NUMSYMBOLS*SYMBOL_W));
                        out_poison_field    = '0;
                    out_byte_cnt_field  = p1_byte_cnt_unpack_field;
                    out_size_field      = p1_burst_size;
                        out_user_data_field = '0;
                 end
            end else begin // the WA is on reponse path and default: PACKING = 1
                    if (in_size_field < in_ori_size_field) begin 
                    out_data_field      = data_reg;
                    out_data_field[p1_shift_correct_ouput_segments*IN_DATA_W +: IN_DATA_W] = p1_data_field;
                            out_poison_field = '0;
                    out_address_field   = p1_address_field & out_address_field_mask;
                    out_size_field      = p1_burst_size;
                    out_byte_cnt_field  = p1_byte_cnt_field;
                        out_user_data_field      = '0;
                end else begin // narrow transaction on command path, reponse packet will not packed
                    out_data_field      = (p1_data_field << (p1_shift_correct_ouput_segments *IN_NUMSYMBOLS*SYMBOL_W));
                        out_poison_field    = '0;
                    out_byte_cnt_field  = p1_byte_cnt_field;
                    out_size_field      = p1_burst_size;
                        out_user_data_field = '0;
                end
            end

           if (in_size_field < in_ori_size_field) begin // downsize happen on command path, the response need packing
                // Response merging: rules: DECERR(11) > SLVERR (10) > OKAY (00)
                // EXOKAY will not happen on merging
                out_response_status_field = '0;
                if (response_status_reg >= p1_response_status_field) begin
                    out_response_status_field = response_status_reg;
                end else begin
                    out_response_status_field = p1_response_status_field;
                end
            end else begin // narrow transaction on command path, reponse packet will not packed
                out_response_status_field   = p1_response_status_field;
            end

            out_cmpr_read      = p1_cmpr_read;

            // nothing touches these fields, so assign them
            // directly from the input fields
            out_first_field      = p0_first_field;
            out_mid_field        = p0_mid_field;
            out_last_field       = p0_last_field;
            out_lock_field       = p0_out_lock_field;
            out_channel          = p0_channel;
            out_burst_type_field = p0_burst_type_field;           
         end // always @ *

        //-------------------------------------------------------
        // output byte_cnt, rounded up to alignment with the output-side 
        // address map footprint implied by the input-side access.
        //
        // See "option 3" in Appendix C of
        // merlin_interconnect_architecture_fd_91.doc.
        //-------------------------------------------------------
        reg [NW_BITFORSELECT_L:0] low_addr_bits;

        always @* begin
           low_addr_bits = p1_address_field[NW_BITFORSELECT_L:0];
           
           quantized_byte_cnt_field = low_addr_bits + 
                                      p1_byte_cnt_field + 
                                      {clogb2(OUT_NUMSYMBOLS){1'b1}};
           quantized_byte_cnt_field[NW_BITFORSELECT_L:0] = '0;
        end

         //-------------------------------------------------------
         // Backpressure
         //-------------------------------------------------------
         always @ * begin
            p1_ready = out_ready || ~out_valid;
         end
   
      end // if (OUT_NUMSYMBOLS > IN_NUMSYMBOLS)

      //-------------------------------------------------------
      //-------------------------------------------------------
      // Same Width.  Seems kind of silly, but let's be complete.
      //-------------------------------------------------------
      //-------------------------------------------------------
      if (OUT_NUMSYMBOLS == IN_NUMSYMBOLS)  begin
   
         always @* begin
            in_ready                    = out_ready;
            out_valid                   = in_valid;
            out_channel                 = in_channel;
            out_startofpacket           = in_startofpacket;
            out_endofpacket             = in_endofpacket;
            out_size_field              = in_size_field;
            out_data_field              = in_data_field;
            out_byteen_field            = in_byteen_field;
            out_address_field           = in_address_field;
            out_byte_cnt_field          = in_byte_cnt_field;
            out_response_status_field   = in_response_status_field;
            out_lock_field              = in_lock_field;
            out_burst_type_field        = in_burst_type_field;            
            out_cmpr_read               = in_cmpr_read;
            out_first_field             = in_first_field;
            out_mid_field               = in_mid_field;
            out_last_field              = in_last_field;            
            if (ROLE_BASED_USER) begin
               out_poison_field            = in_poison_field;
               out_datachk_field           = in_datachk_field;
               out_user_data_field         = in_user_data_field;
            end
            else begin
               out_poison_field            = '0;
               out_datachk_field           = '0;
               out_user_data_field         = '0;
            end
         end // always @ *
   
      end // if (OUT_NUMSYMBOLS == IN_NUMSYMBOLS)

   endgenerate

   // ---------------------------------------
   // Output Field Mapping
   //
   // Conditionally assign the pseudo-fields. Assign address and size 
   // last, because they partly override the pseudo-fields.
   // ---------------------------------------
   always @* begin
      if (FIRST_EXISTS)
          out_data[OUT_FIRST_H:OUT_FIRST_L] = out_first_field;
      if (MID_EXISTS)
          out_data[OUT_MID_H:OUT_MID_L]     = out_mid_field;
      if (LAST_EXISTS)
          out_data[OUT_LAST_H:OUT_LAST_L]   = out_last_field;

      out_data[OUT_PKT_BURST_SIZE_H      : OUT_PKT_BURST_SIZE_L     ] = out_size_field;
      out_data[OUT_PKT_DATA_H            : OUT_PKT_DATA_L           ] = out_data_field;
      out_data[OUT_PKT_BYTEEN_H          : OUT_PKT_BYTEEN_L         ] = out_byteen_field;
      out_data[OUT_PKT_ADDR_H            : OUT_PKT_ADDR_L           ] = out_address_field;
      out_data[OUT_PKT_BYTE_CNT_H        : OUT_PKT_BYTE_CNT_L       ] = out_byte_cnt_field;
      out_data[OUT_PKT_TRANS_COMPRESSED_READ                        ] = out_cmpr_read;
      out_data[OUT_PKT_TRANS_EXCLUSIVE                              ] = out_lock_field;
      out_data[OUT_PKT_BURST_TYPE_H      : OUT_PKT_BURST_TYPE_L     ] = out_burst_type_field;
      out_data[OUT_PKT_RESPONSE_STATUS_H : OUT_PKT_RESPONSE_STATUS_L] = out_response_status_field;     
      if (ROLE_BASED_USER) begin
         out_data[OUT_PKT_POISON_H          : OUT_PKT_POISON_L         ] = out_poison_field;
         out_data[OUT_PKT_DATACHK_H         : OUT_PKT_DATACHK_L        ] = out_datachk_field;
         out_data[OUT_PKT_SAI_H             : OUT_PKT_SAI_L            ] = out_sai_field;
         out_data[OUT_PKT_ADDRCHK_H         : OUT_PKT_ADDRCHK_L        ] = out_addrchk_field;     
         if(BITSPERBYTE) 
             out_data[OUT_PKT_USER_DATA_H     : OUT_PKT_USER_DATA_L     ] = out_user_data_field;
         else 
             out_data[OUT_PKT_USER_DATA_H     : OUT_PKT_USER_DATA_L     ] = '0;
      end
   end // always @ *

endmodule // width_adapter


