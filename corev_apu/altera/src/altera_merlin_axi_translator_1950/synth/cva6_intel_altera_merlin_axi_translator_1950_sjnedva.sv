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


// AXI Translator
//
// Convert "incomplete" AXI4 interface to
// a "complete" AXI4 interface that connect to network side
//
// Adapts between an AXI master and slave that 
// are almost symmetric, with the following
// exceptions:
//
// the master's address width >= the slave's address width
// the master's id width <= the slave's id width
//
// The s0 interface on this component connects to the master,
// and the m0 interface connects to the slave.
//
// The adaptation logic is minimal in these cases, so this
// component is used instead of the heavier network
// interfaces.
// -----------------------------------------
`timescale 1 ns / 1 ns

module cva6_intel_altera_merlin_axi_translator_1950_sjnedva
#( 
    // ----------------
    // Interface parameters
    // ----------------
    parameter S0_ID_WIDTH           = 4,
              M0_ID_WIDTH           = 8,
              M0_ADDR_WIDTH         = 32,
              S0_ADDR_WIDTH         = 32,
              DATA_WIDTH            = 32,
              M0_SAI_WIDTH          = 4, 
              S0_SAI_WIDTH          = 4,
              M0_USER_ADDRCHK_WIDTH = 4, 
              S0_USER_ADDRCHK_WIDTH = 4,
              S0_WRITE_ADDR_USER_WIDTH  = 64,
              S0_READ_ADDR_USER_WIDTH   = 64,
              M0_WRITE_ADDR_USER_WIDTH  = 64,
              M0_READ_ADDR_USER_WIDTH   = 64,
              M0_WRITE_DATA_USER_WIDTH            = 64,
              M0_WRITE_RESPONSE_DATA_USER_WIDTH   = 64,
              M0_READ_DATA_USER_WIDTH             = 64,
              S0_WRITE_DATA_USER_WIDTH            = 64,
              S0_WRITE_RESPONSE_DATA_USER_WIDTH   = 64,
              S0_READ_DATA_USER_WIDTH             = 64,
              M0_AXI_VERSION        = "AXI3",
              S0_AXI_VERSION        = "AXI3",
   // ---------------
   // Master parameters
   // ---------------
              USE_S0_AWUSER        = 0,
              USE_S0_ARUSER        = 0,
              USE_S0_WUSER         = 0,
              USE_S0_RUSER         = 0,
              USE_S0_BUSER         = 0,
              USE_S0_AWID          = 0,
              USE_S0_AWREGION      = 0,
              USE_S0_AWSIZE        = 0,
              USE_S0_AWBURST       = 0,
              USE_S0_AWLEN         = 0,
              USE_S0_AWLOCK        = 0,
              USE_S0_AWCACHE       = 0,
              USE_S0_AWQOS         = 0,

              USE_S0_WSTRB         = 0,
   
              USE_S0_BID           = 0,
              USE_S0_BRESP         = 0,
              USE_S0_ARID          = 0,
              USE_S0_ARREGION      = 0,
              USE_S0_ARSIZE        = 0,
              USE_S0_ARBURST       = 0,
              USE_S0_ARLEN         = 0,
              USE_S0_ARLOCK        = 0,
              USE_S0_ARCACHE       = 0,
              USE_S0_ARQOS         = 0,
   
              USE_S0_RID           = 0,
              USE_S0_RRESP         = 0,
              USE_S0_RLAST         = 0,
              S0_BURST_LENGTH_WIDTH = 8,
              S0_LOCK_WIDTH         = 1,
              
              //AXI-USER Global signals enables
              USE_S0_AWUSER_ADDRCHK = 0,
              USE_S0_AWUSER_SAI     = 0,
              USE_S0_ARUSER_SAI     = 0,
              USE_S0_ARUSER_ADDRCHK = 0,
              USE_S0_WUSER_DATACHK  = 0,
              USE_S0_WUSER_DATA     = 0,
              USE_S0_WUSER_POISON   = 0,
              USE_S0_RUSER_DATACHK  = 0,
              USE_S0_RUSER_DATA     = 0,
              USE_S0_RUSER_POISON   = 0,
              
              REGENERATE_ADDRCHK    = 0,                      
              ROLE_BASED_USER       = 0,                      
   //-----------------
   // Slave parameters
   //-----------------
              USE_M0_AWREGION      = 1,
              USE_M0_AWLOCK        = 1,
              USE_M0_AWPROT        = 1,
              USE_M0_AWCACHE       = 1,
              USE_M0_AWQOS         = 1,

              USE_M0_WLAST         = 1,
              USE_M0_BRESP         = 1,

              USE_M0_ARREGION      = 1,
              USE_M0_ARLOCK        = 1,
              USE_M0_ARPROT        = 1,
              USE_M0_ARCACHE       = 1,
              USE_M0_ARQOS         = 1,

              USE_M0_RRESP         = 1,
              USE_M0_AWUSER        = 0,
              USE_M0_ARUSER        = 0,
              USE_M0_WUSER         = 0,
              USE_M0_RUSER         = 0,
              USE_M0_BUSER         = 0,
              
              //AXI-USER Global signals enables
              USE_M0_AWUSER_ADDRCHK = 0,
              USE_M0_AWUSER_SAI     = 0,
              USE_M0_ARUSER_SAI     = 0,              
              USE_M0_ARUSER_ADDRCHK = 0,
              USE_M0_WUSER_DATACHK  = 0,
              USE_M0_WUSER_DATA     = 0,
              USE_M0_WUSER_POISON   = 0,
              USE_M0_RUSER_DATACHK  = 0,
              USE_M0_RUSER_DATA     = 0,
              USE_M0_RUSER_POISON   = 0,
              
              M0_BURST_LENGTH_WIDTH= 8,
              M0_LOCK_WIDTH        = 2,

              ACE_LITE_SUPPORT  = 0,
              USER_DATA_WIDTH   = 1,
    
    // ----------------
    // Derived parameters
    // ----------------
              // Parity check generation
              // Rule: calcuate parity if input is invalid (terminated with 0s) and output is required
              // Otherwise, just pass-thru the input

              /* |----------+-------------+-------------| */
              /* | Signal   | input       | output      | */
              /* |----------+-------------+-------------| */
              /* | wuser_datachk | s0_wuser_datachk | m0_wuser_datachk | */
              /* | ruser_datachk | m0_ruser_datachk | s0_ruser_datachk | */
              /* |----------+-------------+-------------| */
              CALCULATE_WUSER_DATACHK =  USE_S0_WUSER_DATACHK==0 && USE_M0_WUSER_DATACHK ==1, 
              CALCULATE_RUSER_DATACHK =  USE_S0_RUSER_DATACHK==1 && USE_M0_RUSER_DATACHK ==0,
              
              CALCULATE_AWUSER_ADDRCHK =  USE_S0_AWUSER_ADDRCHK==0 && USE_M0_AWUSER_ADDRCHK ==1, 
              CALCULATE_ARUSER_ADDRCHK =  USE_S0_ARUSER_ADDRCHK==0 && USE_M0_ARUSER_ADDRCHK ==1,              
              
              SKIP_USER_ADDRCHK_CAL =  ((M0_ADDR_WIDTH/8) - M0_USER_ADDRCHK_WIDTH > 1)  , 
              
              S0_PADDING_ZERO      = (S0_USER_ADDRCHK_WIDTH*8) - S0_ADDR_WIDTH,
              M0_PADDING_ZERO      = (M0_USER_ADDRCHK_WIDTH*8) - M0_ADDR_WIDTH,
              
              M0_PARITY_ADDR_WIDTH = M0_ADDR_WIDTH + M0_PADDING_ZERO,

              DATACHK_WIDTH     = DATA_WIDTH / 8,
              POISON_WIDTH      = (DATA_WIDTH + 64 -1) / 64, // ceil(DATA_WIDTH/64) workaround              
              
              STROBE_WIDTH      = DATA_WIDTH / 8,
              BURST_SIZE        = $clog2(STROBE_WIDTH)
)
(
    // ----------------
    // Clock & reset
    // ----------------
    input                                          aclk,
    input                                          aresetn,
                         
    // ----------------
    // Master-facing AXI interface
    // ----------------
    input [S0_ID_WIDTH-1:0]                        s0_awid,
    input [S0_ADDR_WIDTH-1:0]                      s0_awaddr,
    input [S0_BURST_LENGTH_WIDTH-1:0]              s0_awlen, 
    input [2:0]                                    s0_awsize,
    input [1:0]                                    s0_awburst,
    input [S0_LOCK_WIDTH-1:0]                      s0_awlock,
    input [3:0]                                    s0_awcache,
    input [2:0]                                    s0_awprot,
    input [S0_WRITE_ADDR_USER_WIDTH-1:0]           s0_awuser,
    input [3:0]                                    s0_awqos,
    input [3:0]                                    s0_awregion, 
    input                                          s0_awvalid,
    output                                         s0_awready,

    input [S0_ID_WIDTH-1:0]                        s0_wid,
    input [DATA_WIDTH-1:0]                         s0_wdata,
    input [STROBE_WIDTH-1:0]                       s0_wstrb,
    input                                          s0_wlast,
    input [S0_WRITE_DATA_USER_WIDTH-1:0]           s0_wuser,
    input                                          s0_wvalid,
    output                                         s0_wready,

    output reg [S0_ID_WIDTH-1:0]                   s0_bid,
    output reg [1:0]                               s0_bresp,
    output [S0_WRITE_RESPONSE_DATA_USER_WIDTH-1:0] s0_buser, 
    output                                         s0_bvalid,
    input                                          s0_bready, 

    input [S0_ID_WIDTH-1:0]                        s0_arid,
    input [S0_ADDR_WIDTH-1:0]                      s0_araddr,
    input [S0_BURST_LENGTH_WIDTH-1:0]              s0_arlen,
    input [2:0]                                    s0_arsize,
    input [1:0]                                    s0_arburst,
    input [S0_LOCK_WIDTH-1:0]                      s0_arlock,
    input [3:0]                                    s0_arcache,
    input [2:0]                                    s0_arprot,
    input [3:0]                                    s0_arqos,
    input [3:0]                                    s0_arregion,
    input [S0_READ_ADDR_USER_WIDTH-1:0]            s0_aruser,
    input                                          s0_arvalid,
    output                                         s0_arready,

    output reg [S0_ID_WIDTH-1:0]                   s0_rid,
    output [DATA_WIDTH-1:0]                        s0_rdata,
    output reg [1:0]                               s0_rresp,
    output reg                                     s0_rlast,
    output [S0_READ_DATA_USER_WIDTH-1:0]           s0_ruser,
    output                                         s0_rvalid,
    input                                          s0_rready,

    input [1:0]                                    s0_ardomain, 
    input [3:0]                                    s0_arsnoop,  
    input [1:0]                                    s0_arbar,   
 
    input [1:0]                                    s0_awdomain, 
    input [2:0]                                    s0_awsnoop,  
    input [1:0]                                    s0_awbar,    
    input                                          s0_awunique,
    
    input [S0_USER_ADDRCHK_WIDTH-1:0]              s0_awuser_addrchk,
    input [S0_SAI_WIDTH-1:0]                       s0_awuser_sai,
    input [S0_SAI_WIDTH-1:0]                       s0_aruser_sai,
    input [S0_USER_ADDRCHK_WIDTH-1:0]              s0_aruser_addrchk,
    input [DATACHK_WIDTH-1:0]                      s0_wuser_datachk,
    input [USER_DATA_WIDTH-1:0]                    s0_wuser_data,
    input [POISON_WIDTH-1:0]                       s0_wuser_poison,
    output [DATACHK_WIDTH-1:0]                     s0_ruser_datachk,
    output [USER_DATA_WIDTH-1:0]                   s0_ruser_data,
    output [POISON_WIDTH-1:0]                      s0_ruser_poison,

    // ----------------
    // Slave-facing AXI interface
    // ----------------
    output reg [M0_ID_WIDTH-1:0]                   m0_awid,
    output [M0_ADDR_WIDTH-1:0]                     m0_awaddr,
    output reg [M0_BURST_LENGTH_WIDTH-1:0]         m0_awlen, 
    output reg [2:0]                               m0_awsize,
    output reg [1:0]                               m0_awburst,
    output reg [M0_LOCK_WIDTH-1:0]                 m0_awlock,
    output reg [3:0]                               m0_awcache,
    output reg [2:0]                               m0_awprot,
    output reg [3:0]                               m0_awqos,
    output reg [3:0]                               m0_awregion,
    output                                         m0_awvalid,
    output [M0_WRITE_ADDR_USER_WIDTH-1:0]          m0_awuser,
    input                                          m0_awready,

    output reg [M0_ID_WIDTH-1:0]                   m0_wid,
    output [DATA_WIDTH-1:0]                        m0_wdata,
    output reg [STROBE_WIDTH-1:0]                  m0_wstrb,
    output reg                                     m0_wlast,
    output                                         m0_wvalid,
    output [M0_WRITE_DATA_USER_WIDTH-1:0]          m0_wuser, 
    input                                          m0_wready,

    input [M0_ID_WIDTH-1:0]                        m0_bid,
    input [1:0]                                    m0_bresp,
    input [M0_WRITE_RESPONSE_DATA_USER_WIDTH-1:0]  m0_buser, 
    input                                          m0_bvalid,
    output                                         m0_bready,

    output reg [M0_ID_WIDTH-1:0]                   m0_arid,
    output [M0_ADDR_WIDTH-1:0]                     m0_araddr,
    output reg [M0_BURST_LENGTH_WIDTH-1:0]         m0_arlen,
    output reg [2:0]                               m0_arsize,
    output reg [1:0]                               m0_arburst,
    output reg [M0_LOCK_WIDTH-1:0]                 m0_arlock,
    output reg [3:0]                               m0_arcache,
    output reg [3:0]                               m0_arqos,
    output reg [3:0]                               m0_arregion,
    output reg [2:0]                               m0_arprot,
    output                                         m0_arvalid,
    output [M0_READ_ADDR_USER_WIDTH-1:0]           m0_aruser,
    input                                          m0_arready,

    input [M0_ID_WIDTH-1:0]                        m0_rid,
    input [DATA_WIDTH-1:0]                         m0_rdata,
    input [1:0]                                    m0_rresp,
    input [M0_READ_DATA_USER_WIDTH-1:0]            m0_ruser,
    input                                          m0_rlast,
    input                                          m0_rvalid,
    output                                         m0_rready,

    output [1:0]                                   m0_ardomain, 
    output [3:0]                                   m0_arsnoop,  
    output [1:0]                                   m0_arbar,   
 
    output [1:0]                                   m0_awdomain, 
    output [2:0]                                   m0_awsnoop,  
    output [1:0]                                   m0_awbar,    
    output                                         m0_awunique,
    
    output [M0_USER_ADDRCHK_WIDTH-1:0]             m0_awuser_addrchk,
    output [M0_SAI_WIDTH-1:0]                      m0_awuser_sai,
    output [M0_SAI_WIDTH-1:0]                      m0_aruser_sai,    
    output [M0_USER_ADDRCHK_WIDTH-1:0]             m0_aruser_addrchk,
    output [DATACHK_WIDTH-1:0]                     m0_wuser_datachk,
    output [USER_DATA_WIDTH-1:0]                   m0_wuser_data,
    output [POISON_WIDTH-1:0]                      m0_wuser_poison,
    input  [DATACHK_WIDTH-1:0]                     m0_ruser_datachk,
    input  [USER_DATA_WIDTH-1:0]                   m0_ruser_data,
    input  [POISON_WIDTH-1:0]                      m0_ruser_poison    


);

    wire                          ar_parity_status;
    wire                          aw_parity_status;
    // -----------------------------------------
    // All we have to do is assign everything through,
    // with special care for id and address.
    // Along with optional signal from AXI4 master
    // pass through or assign default value
    // -----------------------------------------
    // The AXI translator will need handle these cases
    // with different interface at both side: (mostly in 1-1 connection)
    // AXI3 <-> AXI3
    // AXI3 <-> AXI4
    // AXI4 <-> AXI4
    // AXI4 Lite <-> AXI3/AXI4
    // for other mxn with interconnect inserted
    // the translator will have:
    // AXI4/AXI4 Lite <-> "Full" AXI4 
    // -----------------------------------------
    // All these checking condition below apply for AXI4
    // in case AXI3, all parameters will be set and passed
    // correctly from hw.tcl
    // -----------------------------------------
    
    
always_comb
    begin
        if (S0_AXI_VERSION == "AXI3") begin
            // 1-1 system: AXI3 master <-{translator}-> AXI3 slave: 
            // when master and slave size if translator            
            // is both AXI3: almost pass through every signals, care
            // about ID width and address width
            if (M0_AXI_VERSION == "AXI3") begin
                m0_awlen    = s0_awlen;
                m0_awsize   = s0_awsize;
                m0_awburst  = s0_awburst;
                m0_awlock   = s0_awlock;
                m0_awcache  = s0_awcache;
                m0_awprot   = s0_awprot;

                m0_wid      = s0_wid;
                m0_wstrb    = s0_wstrb;
                m0_wlast    = s0_wlast;
                
                m0_arlen    = s0_arlen;
                m0_arsize   = s0_arsize;
                m0_arburst  = s0_arburst;
                m0_arcache  = s0_arcache;
                m0_arprot   = s0_arprot;
                m0_arlock   = s0_arlock;
                
                s0_bresp    = m0_bresp;
                s0_rresp    = m0_rresp;
                s0_rlast    = m0_rlast;
                // Avoid QIS warning
                m0_awregion = '0;
                m0_awqos    = '0;
                m0_arregion = '0;
                m0_arqos    = '0;
                                
                // ID
                m0_awid     =     s0_awid;
                m0_arid     =     s0_arid;
                m0_wid      =     s0_wid;
                // -----------------------------------------
                // Only pass the lower bits of ID through
                // -----------------------------------------
                s0_bid      =     m0_bid[S0_ID_WIDTH - 1 : 0];
                s0_rid      =     m0_rid[S0_ID_WIDTH - 1 : 0];
            end
            // 1-1 system: AXI3 master <-{translator}-> AXI4 slave
            // do some checking on slave side and converstion from AXI3 to AXI4 if needed (ex lock signal width)
            else begin
                // Check option signals in slave side only
                // Signals which are not avaible in AXI3 master, drive with default value
                // These signals are not avaible in AXI3 master, so the translator just assign default value
                // avoid QIS waraning as well
                m0_awregion    = '0;
                m0_awqos       = '0;
                m0_arregion    = '0;
                m0_arqos       = '0;
                
                // Need some converstion for AXI3 and AXI4
                // with: AXLOCK[1:0] =b10 => AXLOCK = 0
                m0_awlock  = s0_awlock[0];
                m0_arlock  = s0_arlock[0];

                // Protection signals: just do assignemnt
                // even the AXI4 slave doesnt use it to avoid QIS warning
                // the Port has been terninated in hw.tcl
                // and these port must be always exist in AXI3 master
                m0_awprot    = s0_awprot;
                m0_arprot    = s0_arprot;
                m0_wlast     = s0_wlast;
                m0_awcache   = s0_awcache;
                m0_arcache   = s0_arcache;
                
                // Pass lower bits of ID
                s0_bid      = m0_bid[S0_ID_WIDTH-1:0];
                s0_rid      = m0_rid[S0_ID_WIDTH-1:0];
                // Avoid QIS warning
                s0_rlast    = m0_rlast;
                // Pass through
                m0_awlen    = s0_awlen;
                m0_awid     = s0_awid;
                m0_arid     = s0_arid;
                m0_awburst  = s0_awburst;
                m0_arburst  = s0_arburst;
                m0_wstrb    = s0_wstrb;
                m0_awsize   = s0_awsize;
                m0_arsize   = s0_arsize;
                m0_arlen    = s0_arlen;
                // AXI3 has no idea about QOS, so set to default for all cases.
                m0_awqos    = '0;
                m0_arqos    = '0;
                
                // AXI3 need WID, so just so it base on AXI3, the AXI4 slave wont read this
                m0_wid      = s0_wid;
            
                if (USE_M0_BRESP)
                    s0_bresp     = m0_bresp;
                else
                    s0_bresp     = 2'b00; //OKAY
                if (USE_M0_RRESP)
                    s0_rresp     = m0_rresp;
                else
                    s0_rresp     = 2'b00; //OKAY
            end // else: !if(M0_AXI_VERSION == "AXI3")
        end // if (S0_AXI_VERSION == "AXI3")
        
        // AXI4 master <-{translator}-> AXI4 slave: cases
        // a) not 1-1 system: the translator can be either "master translator" or "slave translator"
        //    This case, one side will be always as "complete" AXI4
        //    Ex: if translator is at master side: AXI4 master <-{translator}-> [Interconnect Network]
        //        at translator's interface side at Interconnect will be always complete AXI4
        //    So, the translator will take care of optional signals and default value of one side
        // b) 1-1 system: special case: the translator need to check on optional signal for both side of
        //    interface
        // 
        else begin
            // Checking on signals that can be optional for both side
            // NOTE: if slave side use that signal but master side does not
            //       then assign outpur as default value
            //       if slave side does not use that signal, not matter master side
            //       use this or not, just pass through the value (the port has been terminated in hw.tcl)
            //       in HDL file, the port still there, so assign to avoid QIS warning
            //       Same, if both use that signal -> assign through
            //       it helps to reduce if and avoid warning some signal not assigned value
                        
            if ((USE_M0_AWREGION) && (!USE_S0_AWREGION))
                m0_awregion    = '0; //default value
            else
                m0_awregion    = s0_awregion;
                        
            if ((USE_M0_AWLOCK) && (!USE_S0_AWLOCK))
                m0_awlock      = '0;
            else 
                m0_awlock      = s0_awlock;

            if ((USE_M0_AWCACHE) && (!USE_S0_AWCACHE))
                m0_awcache     = '0;
            else
                m0_awcache     = s0_awcache;
            
            if ((USE_M0_AWQOS) && (!USE_S0_AWQOS)) 
                m0_awqos       = '0;
            else
                m0_awqos       = s0_awqos;
        
            if ((USE_S0_BRESP) && (!USE_M0_BRESP))
                s0_bresp       = 2'b00; //OKAY
            else
                s0_bresp       = m0_bresp;
            
            if ((USE_M0_ARREGION) && (!USE_S0_ARREGION))
                m0_arregion    = '0; //default value
            else
                m0_arregion    = s0_arregion;
                        
            if ((USE_M0_ARLOCK) && (!USE_S0_ARLOCK))
                m0_arlock      = '0;
            else 
                m0_arlock      = s0_arlock;

            if ((USE_M0_ARCACHE) && (!USE_S0_ARCACHE))
                m0_arcache     = '0;
            else
                m0_arcache     = s0_arcache;
            
            if ((USE_M0_ARQOS) && (!USE_S0_ARQOS)) 
                m0_arqos       = '0;
            else
                m0_arqos       = s0_arqos;
        
            if ((USE_S0_RRESP) && (!USE_M0_RRESP))
                s0_rresp       = 2'b00; //OKAY
            else
                s0_rresp       = m0_rresp;
        
        
            // Check signal that secific to each side only
            // -- Master side signals
            if (USE_S0_AWID)
                m0_awid    = s0_awid;
            else
                m0_awid    = '0;
            if (USE_S0_AWLEN)
                m0_awlen    = s0_awlen;
            else
                m0_awlen    = '0;
            if (USE_S0_AWSIZE)
                m0_awsize   = s0_awsize;
            else
                m0_awsize   = BURST_SIZE[2:0]; // Number of symbol
            if (USE_S0_AWBURST)
                m0_awburst  = s0_awburst;
            else
                m0_awburst  = 2'b01; // INCR
            if (USE_S0_WSTRB)
                m0_wstrb    = s0_wstrb;
            else
                m0_wstrb    =  {STROBE_WIDTH{1'b1}};

            if (USE_S0_ARID)
                m0_arid    = s0_arid;
            else
                m0_arid    = '0;
            if (USE_S0_ARLEN)
                m0_arlen    = s0_arlen;
            else
                m0_arlen    = '0;
            if (USE_S0_ARSIZE)
                m0_arsize   = s0_arsize;
            else
                m0_arsize   = BURST_SIZE[2:0]; // Number of symbol
            if (USE_S0_ARBURST)
                m0_arburst  = s0_arburst;
            else
                m0_arburst  = 2'b01; // INCR

            // these just assign to avoid warning
            s0_bid          = m0_bid[S0_ID_WIDTH-1:0];
            s0_rid          = m0_rid[S0_ID_WIDTH-1:0];
            s0_rlast        = m0_rlast;
            // AXI4 doesnt have WID but jsut assign a value to avoid QIS warning
            // the port is terminated in hw.tcl
            m0_wid          = '0;
                        
            // Slave side signals
            m0_awprot       = s0_awprot;
            m0_wlast        = s0_wlast;
            m0_arprot       = s0_arprot;
            
            end // else: !if(S0_AXI_VERSION == "AXI3")
        
        // When master is AXI4Lite, the slave either AXI3 or AXI4, we need to set some default values for some signals
        if (S0_AXI_VERSION == "AXI4Lite") begin
            // write address channel
            m0_awid      = '0;
            m0_awlen     = '0; // non-bursting
            m0_awburst   = 2'b01; // INCR
            m0_awsize    = BURST_SIZE[2:0];
            m0_awlock    = '0;
            m0_awcache   = '0;
            m0_awprot    = s0_awprot;
            m0_awqos     = '0;
            m0_awregion  = '0;

            // write data channel
            m0_wid       = '0;
            m0_wlast     = 1'b1; // AXI4 lite always sets this to 1

            //write response channel
            s0_bid       = m0_bid;

            // read address channel
            m0_arid      = '0;
            m0_arlen     = '0;
            m0_arsize    = BURST_SIZE[2:0];
            m0_arburst   = 2'b01;
            m0_arlock    = '0;
            m0_arcache   = '0;
            m0_arprot    = s0_arprot;
            m0_arqos     = '0;
            m0_arregion  = '0;

            // read data channel
            s0_rid       = m0_rid;
            s0_rlast     = 1'b1;
        end // if (S0_AXI_VERSION == "AXI4Lite")
        else begin
            // When slave is AXI4 lite, the other side of the translator will be full AXI4 (AXI3 no translator)
            // Mostly all AXI4 lite signals will back thru, other we write default values
            // Pass back all ID signal, normally AXI4 lite doest support ID but it is optional that it can have if.

            // Pass only lower bits
            s0_bid  = m0_bid [S0_ID_WIDTH-1:0];
            s0_rid  = m0_rid [S0_ID_WIDTH-1:0];
            end // else: !if(S0_AXI_VERSION == "AXI4Lite")
    end // always_comb
    

    // common signals assignment for all cases
    assign m0_awvalid      =     s0_awvalid;
    assign s0_awready      =     m0_awready;
    
    assign m0_wdata        =     s0_wdata;
    assign m0_wvalid       =     s0_wvalid;
    assign s0_wready       =     m0_wready;

    assign m0_arvalid      =     s0_arvalid;
    assign s0_arready      =     m0_arready;

    assign s0_bvalid       =     m0_bvalid;
    assign m0_bready       =     s0_bready;

    assign s0_rdata        =     m0_rdata;
    assign s0_rvalid       =     m0_rvalid;
    assign m0_rready       =     s0_rready;
    // Avoid QIS warning, master address will be always same or larger than slave
    // so only assign enough bit width from master to slave
    assign m0_awaddr       =     s0_awaddr[M0_ADDR_WIDTH-1 :0];
    assign m0_araddr       =     s0_araddr[M0_ADDR_WIDTH-1 :0];
    assign m0_awuser       =     USE_S0_AWUSER ? s0_awuser : '0;
    assign m0_aruser       =     USE_S0_ARUSER ? s0_aruser : '0;
    assign m0_wuser        =     USE_S0_WUSER ? s0_wuser : '0;
    assign s0_buser        =     USE_M0_BUSER ? m0_buser : '0;
    assign s0_ruser        =     USE_M0_RUSER ? m0_ruser : '0;

    assign m0_wuser_poison   =   (USE_S0_WUSER_POISON && ROLE_BASED_USER) ? s0_wuser_poison: 1'b0;
    assign s0_ruser_poison   =   (USE_M0_RUSER_POISON && ROLE_BASED_USER) ? m0_ruser_poison: 1'b0;

    assign m0_wuser_data     =   (USE_S0_WUSER_DATA && ROLE_BASED_USER) ? s0_wuser_data : 1'b0; 
    assign s0_ruser_data     =   (USE_M0_RUSER_DATA && ROLE_BASED_USER) ? m0_ruser_data : 1'b0;
 
    assign m0_awuser_sai     =   (USE_S0_AWUSER_SAI   && ROLE_BASED_USER) ? s0_awuser_sai: 'b0;
    assign m0_aruser_sai     =   (USE_S0_ARUSER_SAI   && ROLE_BASED_USER) ? s0_aruser_sai: 'b0;

    assign m0_ardomain  =  s0_ardomain;
    assign m0_arsnoop   =  s0_arsnoop;
    assign m0_arbar     =  s0_arbar;

    assign m0_awdomain  =  s0_awdomain;
    assign m0_awsnoop   =  s0_awsnoop;
    assign m0_awbar     =  s0_awbar;
    assign m0_awunique  =  s0_awunique;
    
generate
    if (CALCULATE_WUSER_DATACHK && ROLE_BASED_USER) begin
        assign m0_wuser_datachk = calcParity(s0_wdata);
    end
    else if(ROLE_BASED_USER && USE_S0_WUSER_DATACHK) begin
        assign m0_wuser_datachk = s0_wuser_datachk;
    end else begin
        assign m0_wuser_datachk = '0;
    end
    
    if (CALCULATE_RUSER_DATACHK && ROLE_BASED_USER) begin
        assign s0_ruser_datachk = calcParity(m0_rdata);
    end else if(ROLE_BASED_USER && USE_M0_RUSER_DATACHK) begin
        assign s0_ruser_datachk = m0_ruser_datachk;
    end else begin
        assign s0_ruser_datachk = '0;
    end

    if (CALCULATE_AWUSER_ADDRCHK && ROLE_BASED_USER) begin
        assign ar_parity_status = 1'b0;
        if(SKIP_USER_ADDRCHK_CAL) begin
            assign m0_awuser_addrchk = '0;
        end
        else begin
            assign m0_awuser_addrchk = addrcalcParity({{M0_PADDING_ZERO{1'b0}},m0_awaddr});
        end
    end else if(REGENERATE_ADDRCHK) begin
        wire [S0_USER_ADDRCHK_WIDTH-1:0]      expected_awuser_addrchk_parity; 
        
        assign expected_awuser_addrchk_parity = addrcalcParity ( {{S0_PADDING_ZERO{1'b0}},s0_awaddr });
        assign aw_parity_status = (expected_awuser_addrchk_parity == s0_awuser_addrchk) ? 1'b0 : 1'b1;

        assign m0_awuser_addrchk = aw_parity_status ? addrcalc_incorrectParity({{M0_PADDING_ZERO{1'b0}},m0_awaddr}): addrcalcParity({{M0_PADDING_ZERO{1'b0}},m0_awaddr});
    end else if(ROLE_BASED_USER && USE_S0_AWUSER_ADDRCHK) begin
        assign m0_awuser_addrchk = s0_awuser_addrchk;
        assign ar_parity_status = 1'b0;
    end else begin
        assign m0_awuser_addrchk = '0;
        assign ar_parity_status = 1'b0;
    end

    if (CALCULATE_ARUSER_ADDRCHK && ROLE_BASED_USER) begin
        assign aw_parity_status = 1'b0;
        if(SKIP_USER_ADDRCHK_CAL) begin
            assign m0_awuser_addrchk = '0;
        end
        else begin
            assign m0_aruser_addrchk = addrcalcParity({{M0_PADDING_ZERO{1'b0}},m0_araddr});
        end
    end else if(REGENERATE_ADDRCHK) begin
        wire [S0_USER_ADDRCHK_WIDTH-1:0]      expected_aruser_addrchk_parity; 
        
        assign ar_parity_status = (expected_aruser_addrchk_parity == s0_aruser_addrchk) ? 1'b0 : 1'b1;
        assign expected_aruser_addrchk_parity = addrcalcParity ( {{S0_PADDING_ZERO{1'b0}},s0_araddr});

        assign m0_aruser_addrchk = ar_parity_status ? addrcalc_incorrectParity({{M0_PADDING_ZERO{1'b0}},m0_araddr}): addrcalcParity({{M0_PADDING_ZERO{1'b0}},m0_araddr});
    end else if(ROLE_BASED_USER && USE_S0_ARUSER_ADDRCHK) begin
        assign ar_parity_status = 1'b0;
        assign m0_aruser_addrchk = s0_aruser_addrchk;
    end else begin
        assign aw_parity_status = 1'b0;
        assign m0_aruser_addrchk = '0; 
    end
endgenerate;     
    
    // --------------------------------------------------
    //
    // calcParity function: calculate byte-level parity of arbitrary-sized signal
    //
    // --------------------------------------------------

    function reg [DATACHK_WIDTH-1:0] calcParity (
        input [DATA_WIDTH-1:0] data
    );
        for (int i=0; i<DATACHK_WIDTH; i++)
            calcParity[i] = ~(^ data[i*8 +:8]);
    endfunction

   //address parity generation logic 
    function reg [M0_USER_ADDRCHK_WIDTH-1:0] addrcalcParity (
        input [M0_PARITY_ADDR_WIDTH-1:0] addr
    );
        for (int i=0; i<M0_USER_ADDRCHK_WIDTH; i++)
            addrcalcParity[i] = ~(^ addr[i*8 +:8]);
    endfunction

    // --------------------------------------------------
    // addrcalc_incorrectParity: calculates byte-level incorrect parity signal 
    // --------------------------------------------------
    function reg [M0_USER_ADDRCHK_WIDTH-1:0] addrcalc_incorrectParity (
        input [M0_PARITY_ADDR_WIDTH-1:0] addr
     );
        reg [M0_USER_ADDRCHK_WIDTH-1:0]addrcalcParity;

        for (int i=0; i<M0_USER_ADDRCHK_WIDTH; i++)
            addrcalcParity[i] = ~(^ addr[i*8 +:8]);
        addrcalc_incorrectParity = {addrcalcParity[M0_USER_ADDRCHK_WIDTH-1:1],~addrcalcParity[0]}; 
    endfunction
    

endmodule

