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


// (C) 2001-2012 Altera Corporation. All rights reserved.
// Your use of Altera Corporation's design tools, logic functions and other
// software and tools, and its AMPP partner logic functions, and any output
// files any of the foregoing (including device programming or simulation
// files), and any associated documentation or information are expressly subject
// to the terms and conditions of the Altera Program License Subscription
// Agreement, Altera MegaCore Function License Agreement, or other applicable
// license agreement, including, without limitation, that your use is for the
// sole purpose of programming logic devices manufactured by Altera and sold by
// Altera or its authorized distributors.  Please refer to the applicable
// agreement for further details.


// $Id: //acds/main/ip/merlin/altera_merlin_burst_adapter/altera_merlin_burst_adapter.sv#68 $
// $Revision: #68 $
// $Date: 2014/01/23 $

`timescale 1 ns / 1 ns

// -------------------------------------------------------
// Adapter for uncompressed transactions only. This adapter will
// typically be used to adapt burst length for non-bursting 
// wide to narrow Avalon links.
// -------------------------------------------------------
module altera_merlin_burst_adapter_uncompressed_only
#(
    parameter 
    PKT_BYTE_CNT_H  = 5,
    PKT_BYTE_CNT_L  = 0,
    PKT_BYTEEN_H    = 83,
    PKT_BYTEEN_L    = 80,
    ST_DATA_W       = 84,
    ST_CHANNEL_W    = 8
)
(
    input clk,
    input reset,

    // -------------------
    // Command Sink (Input)
    // -------------------
    input                           sink0_valid,
    input  [ST_DATA_W-1 : 0]        sink0_data,
    input  [ST_CHANNEL_W-1 : 0]     sink0_channel,
    input                           sink0_startofpacket,
    input                           sink0_endofpacket,
    output reg                      sink0_ready,

    // -------------------
    // Command Source (Output)
    // -------------------
    output reg                      source0_valid,
    output reg [ST_DATA_W-1    : 0] source0_data,
    output reg [ST_CHANNEL_W-1 : 0] source0_channel,
    output reg                      source0_startofpacket,
    output reg                      source0_endofpacket,
    input                           source0_ready
);
    localparam
        PKT_BYTE_CNT_W = PKT_BYTE_CNT_H - PKT_BYTE_CNT_L + 1,
        NUM_SYMBOLS    = PKT_BYTEEN_H - PKT_BYTEEN_L + 1;

    wire [PKT_BYTE_CNT_W - 1 : 0] num_symbols_sig = NUM_SYMBOLS[PKT_BYTE_CNT_W - 1 : 0];

    always_comb begin : source0_data_assignments
        source0_valid         = sink0_valid;
        source0_channel       = sink0_channel;
        source0_startofpacket = sink0_startofpacket;
        source0_endofpacket   = sink0_endofpacket;

        source0_data          = sink0_data;
        source0_data[PKT_BYTE_CNT_H : PKT_BYTE_CNT_L] = num_symbols_sig;

        sink0_ready = source0_ready;
    end

endmodule



`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "GdrtC8041f37ha52Ko+Jde808iDyKA+ht5m5AuKQCsm3cRPQscDvF+wBgbawWOxUtCRI9a/tnC6AChwO+BxfmEV2UK9ncMFAL//YMEMfhylNbbg+DkYNRltJ3oLac/x0CKLYUz0kP213IDPHPJdDrn2XWjqkg2d8WjL/DUsL13IJgiL6ltB1LI/UYnSBUYY+yK6OwicfHT3EuyorZ8lWql/zzL2Fl1behLT6A47M1qi44zg2/l33guJiqM98UvNerFZud/HkMNHBGPjwk3bwNTrItRK/xwT9+67k1gpQ0lNOzkFqIKtDLX4D5xZJaOTfxF01U/0HspM2kEFjnXWVthjie6duIIBB61yFuiVC+Js7/okD8lgZazTs0ekuxjymO6JTQ/jnin6O3f8m/GdULiQM+6XRkWDkXKq5+YdtxC/tWtzZHXQyVUmxibo6ADkz4bObuE7bH+rlcBRcdfNUA1OTkbVbIMqKT194MxnDeCluqYvKSlZmtKE4c582JPZDJCm64XAsiKE7JsQXEZqZS6jIZI7r++Jm3RrA74dUJuwQMSpEP/qz3S6mfMGiQ9sV685GVGjXUjG92eI8AbinO0ugcyOEgKF0ozxQahqgXNqRYp5fl2vTz/X4E11YdL3x/s3GrWNEyP0Aq71JAc5b3IwS6f8N1RYPTorQiJhOW6S61OvOBJnL66xm99SZi7tJt8UiQfjj7wd/QsLl6/rtr0cRfrm6jrpnXwJuV5QIkKivsAOehIdRUbJ5FVjGwf/R85EtSTMOcQONuiWo2EZ4WaZR0Zr3YBilMd1t8t7wpC6EBNkGLnR5SN08K7hQfc74w21I8qP7rmwGyIf/N1uAKTw9N6fYehgT4lQNqXaI6rCxeY25OClEebB7RPeu10UEcL54CWUU4im2PfoD1mZZmIrcl26dKs9cDNVclc4NOAUmySQOh8TtqeAlIjBnyJpuqTpaUM2wkGTh7Ze7dDs3dHDg4uIl9uk0WADtiqeABp8mqbjnXzCkuSDi4+lB6eqF"
`endif