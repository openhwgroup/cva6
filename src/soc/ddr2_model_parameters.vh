/****************************************************************************************
*
*   Disclaimer   This software code and all associated documentation, comments or other
*  of Warranty:  information (collectively "Software") is provided "AS IS" without
*                warranty of any kind. MICRON TECHNOLOGY, INC. ("MTI") EXPRESSLY
*                DISCLAIMS ALL WARRANTIES EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
*                TO, NONINFRINGEMENT OF THIRD PARTY RIGHTS, AND ANY IMPLIED WARRANTIES
*                OF MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. MTI DOES NOT
*                WARRANT THAT THE SOFTWARE WILL MEET YOUR REQUIREMENTS, OR THAT THE
*                OPERATION OF THE SOFTWARE WILL BE UNINTERRUPTED OR ERROR-FREE.
*                FURTHERMORE, MTI DOES NOT MAKE ANY REPRESENTATIONS REGARDING THE USE OR
*                THE RESULTS OF THE USE OF THE SOFTWARE IN TERMS OF ITS CORRECTNESS,
*                ACCURACY, RELIABILITY, OR OTHERWISE. THE ENTIRE RISK ARISING OUT OF USE
*                OR PERFORMANCE OF THE SOFTWARE REMAINS WITH YOU. IN NO EVENT SHALL MTI,
*                ITS AFFILIATED COMPANIES OR THEIR SUPPLIERS BE LIABLE FOR ANY DIRECT,
*                INDIRECT, CONSEQUENTIAL, INCIDENTAL, OR SPECIAL DAMAGES (INCLUDING,
*                WITHOUT LIMITATION, DAMAGES FOR LOSS OF PROFITS, BUSINESS INTERRUPTION,
*                OR LOSS OF INFORMATION) ARISING OUT OF YOUR USE OF OR INABILITY TO USE
*                THE SOFTWARE, EVEN IF MTI HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH
*                DAMAGES. Because some jurisdictions prohibit the exclusion or
*                limitation of liability for consequential or incidental damages, the
*                above limitation may not apply to you.
*
*                Copyright 2003 Micron Technology, Inc. All rights reserved.
*
****************************************************************************************/

    // Timing parameters based on Speed Grade

                                          // SYMBOL UNITS DESCRIPTION
                                          // ------ ----- -----------
`ifdef x256Mb

    `ifdef sg187E
        parameter TCK_MIN          =    1875; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =      90; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =      75; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     180; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     132; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     157; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     175; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     188; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     250; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     425; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     250; // tQHS   ps    Data hold skew factor
        parameter TAC              =     350; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =       0; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =      75; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     300; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     175; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     125; // tIS    ps    Input Setup Time
        parameter TIH              =     200; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   13125; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   13125; // tRP    ps    Precharge command period
        parameter TRPA             =   13125; // tRPA   ps    Precharge All period
        parameter TXARDS           =      10; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       3; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       3; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       4; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      11; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   13125; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25E
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12500; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12500; // tRP    ps    Precharge command period
        parameter TRPA             =   12500; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12500; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3E
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12000; // tRP    ps    Precharge command period
        parameter TRPA             =   12000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg37E
        parameter TCK_MIN          =    3750; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     400; // tQHS   ps    Data hold skew factor
        parameter TAC              =     500; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     225; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     450; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     300; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     250; // tIS    ps    Input Setup Time
        parameter TIH              =     375; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else //`define sg5E
        parameter TCK_MIN          =    5000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     150; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     450; // tQHS   ps    Data hold skew factor
        parameter TAC              =     600; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     150; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     275; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     500; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     350; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     350; // tIS    ps    Input Setup Time
        parameter TIH              =     475; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =   10000; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `endif `endif `endif `endif `endif `endif

    `ifdef x16
      `ifdef sg187E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   50000; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `else // x4, x8
      `ifdef sg187E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   37500; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `endif

        // Timing Parameters

        // Mode Register
        parameter AL_MIN           =       0; // AL     tCK   Minimum Additive Latency
        parameter AL_MAX           =       6; // AL     tCK   Maximum Additive Latency
        parameter CL_MIN           =       3; // CL     tCK   Minimum CAS Latency
        parameter CL_MAX           =       7; // CL     tCK   Maximum CAS Latency
        parameter WR_MIN           =       2; // WR     tCK   Minimum Write Recovery
        parameter WR_MAX           =       8; // WR     tCK   Maximum Write Recovery
        parameter BL_MIN           =       4; // BL     tCK   Minimum Burst Length
        parameter BL_MAX           =       8; // BL     tCK   Minimum Burst Length
        // Clock
        parameter TCK_MAX          =    8000; // tCK    ps    Maximum Clock Cycle Time
        parameter TCH_MIN          =    0.48; // tCH    tCK   Minimum Clock High-Level Pulse Width
        parameter TCH_MAX          =    0.52; // tCH    tCK   Maximum Clock High-Level Pulse Width
        parameter TCL_MIN          =    0.48; // tCL    tCK   Minimum Clock Low-Level Pulse Width
        parameter TCL_MAX          =    0.52; // tCL    tCK   Maximum Clock Low-Level Pulse Width
        // Data
        parameter TLZ              =     TAC; // tLZ    ps    Data-out low-impedance window from CK/CK#
        parameter THZ              =     TAC; // tHZ    ps    Data-out high impedance window from CK/CK#
        parameter TDIPW            =    0.35; // tDIPW  tCK   DQ and DM input Pulse Width
        // Data Strobe
        parameter TDQSH            =    0.35; // tDQSH  tCK   DQS input High Pulse Width
        parameter TDQSL            =    0.35; // tDQSL  tCK   DQS input Low Pulse Width
        parameter TDSS             =    0.20; // tDSS   tCK   DQS falling edge to CLK rising (setup time)
        parameter TDSH             =    0.20; // tDSH   tCK   DQS falling edge from CLK rising (hold time)
        parameter TWPRE            =    0.35; // tWPRE  tCK   DQS Write Preamble
        parameter TWPST            =    0.40; // tWPST  tCK   DQS Write Postamble
        parameter TDQSS            =    0.25; // tDQSS  tCK   Rising clock edge to DQS/DQS# latching transition
        // Command and Address
        parameter TIPW             =     0.6; // tIPW   tCK   Control and Address input Pulse Width
        parameter TCCD             =       2; // tCCD   tCK   Cas to Cas command delay
        parameter TRAS_MIN         =   40000; // tRAS   ps    Minimum Active to Precharge command time
        parameter TRAS_MAX         =70000000; // tRAS   ps    Maximum Active to Precharge command time
        parameter TRTP             =    7500; // tRTP   ps    Read to Precharge command delay
        parameter TWR              =   15000; // tWR    ps    Write recovery time
        parameter TMRD             =       2; // tMRD   tCK   Load Mode Register command cycle time
        parameter TDLLK            =     200; // tDLLK  tCK   DLL locking time
        // Refresh
        parameter TRFC_MIN         =   75000; // tRFC   ps    Refresh to Refresh Command interval minimum value
        parameter TRFC_MAX         =70000000; // tRFC   ps    Refresh to Refresh Command Interval maximum value
        // Self Refresh
        parameter TXSNR   = TRFC_MIN + 10000; // tXSNR  ps    Exit self refesh to a non-read command
        parameter TXSRD            =     200; // tXSRD  tCK   Exit self refresh to a read command
        parameter TISXR            =     TIS; // tISXR  ps    CKE setup time during self refresh exit.
        // ODT
        parameter TAOND            =       2; // tAOND  tCK   ODT turn-on delay
        parameter TAOFD            =     2.5; // tAOFD  tCK   ODT turn-off delay
        parameter TAONPD           =    2000; // tAONPD ps    ODT turn-on (precharge power-down mode)
        parameter TAOFPD           =    2000; // tAOFPD ps    ODT turn-off (precharge power-down mode)
        parameter TMOD             =   12000; // tMOD   ps    ODT enable in EMR to ODT pin transition
        // Power Down
        parameter TCKE             =       3; // tCKE   tCK   CKE minimum high or low pulse width

        // Size Parameters based on Part Width

    `ifdef x4
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter ROW_BITS         =      13; // Number of Address bits
        parameter COL_BITS         =      11; // Number of Column bits
        parameter DQ_BITS          =       4; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else `ifdef x8
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter ROW_BITS         =      13; // Number of Address bits
        parameter COL_BITS         =      10; // Number of Column bits
        parameter DQ_BITS          =       8; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else //`define x16
        parameter DM_BITS          =       2; // Number of Data Mask bits
        parameter ROW_BITS         =      13; // Number of Address bits
        parameter COL_BITS         =       9; // Number of Column bits
        parameter DQ_BITS          =      16; // Number of Data bits
        parameter DQS_BITS         =       2; // Number of Dqs bits
        parameter TRRD             =   10000; // tRRD   Active bank a to Active bank b command time
    `endif `endif

    `ifdef QUAD_RANK
        `define DUAL_RANK // also define DUAL_RANK
        parameter CS_BITS          =       4; // Number of Chip Select Bits
        parameter RANKS            =       4; // Number of Chip Select Bits
    `else `ifdef DUAL_RANK
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       2; // Number of Chip Select Bits
    `else
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       1; // Number of Chip Select Bits
    `endif `endif

        // Size Parameters
        parameter BA_BITS          =       2; // Set this parmaeter to control how many Bank Address bits
        parameter ADDR_BITS        =      13; // Address Bits
        parameter MEM_BITS         =      15; // Number of write data bursts can be stored in memory.  The default is 2^10=1024.
        parameter AP               =      10; // the address bit that controls auto-precharge and precharge-all
        parameter BL_BITS          =       3; // the number of bits required to count to MAX_BL
        parameter BO_BITS          =       2; // the number of Burst Order Bits

`else `ifdef x512Mb

    `ifdef sg187E
        parameter TCK_MIN          =    1875; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =      90; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =      75; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     180; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     132; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     157; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     175; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     188; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     250; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     425; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     250; // tQHS   ps    Data hold skew factor
        parameter TAC              =     350; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =       0; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =      75; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     300; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     175; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     125; // tIS    ps    Input Setup Time
        parameter TIH              =     200; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   13125; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   13125; // tRP    ps    Precharge command period
        parameter TRPA             =   13125; // tRPA   ps    Precharge All period
        parameter TXARDS           =      10; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       3; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       3; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       4; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      11; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   13125; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25E
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12500; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12500; // tRP    ps    Precharge command period
        parameter TRPA             =   12500; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12500; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3E
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12000; // tRP    ps    Precharge command period
        parameter TRPA             =   12000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg37E
        parameter TCK_MIN          =    3750; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     400; // tQHS   ps    Data hold skew factor
        parameter TAC              =     500; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     225; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     450; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     300; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     250; // tIS    ps    Input Setup Time
        parameter TIH              =     375; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else //`define sg5E
        parameter TCK_MIN          =    5000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     150; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     450; // tQHS   ps    Data hold skew factor
        parameter TAC              =     600; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     150; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     275; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     500; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     350; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     350; // tIS    ps    Input Setup Time
        parameter TIH              =     475; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =   10000; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `endif `endif `endif `endif `endif `endif

    `ifdef x16
      `ifdef sg187E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   50000; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `else // x4, x8
      `ifdef sg187E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   37500; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `endif

        // Timing Parameters

        // Mode Register
        parameter AL_MIN           =       0; // AL     tCK   Minimum Additive Latency
        parameter AL_MAX           =       6; // AL     tCK   Maximum Additive Latency
        parameter CL_MIN           =       3; // CL     tCK   Minimum CAS Latency
        parameter CL_MAX           =       7; // CL     tCK   Maximum CAS Latency
        parameter WR_MIN           =       2; // WR     tCK   Minimum Write Recovery
        parameter WR_MAX           =       8; // WR     tCK   Maximum Write Recovery
        parameter BL_MIN           =       4; // BL     tCK   Minimum Burst Length
        parameter BL_MAX           =       8; // BL     tCK   Minimum Burst Length
        // Clock
        parameter TCK_MAX          =    8000; // tCK    ps    Maximum Clock Cycle Time
        parameter TCH_MIN          =    0.48; // tCH    tCK   Minimum Clock High-Level Pulse Width
        parameter TCH_MAX          =    0.52; // tCH    tCK   Maximum Clock High-Level Pulse Width
        parameter TCL_MIN          =    0.48; // tCL    tCK   Minimum Clock Low-Level Pulse Width
        parameter TCL_MAX          =    0.52; // tCL    tCK   Maximum Clock Low-Level Pulse Width
        // Data
        parameter TLZ              =     TAC; // tLZ    ps    Data-out low-impedance window from CK/CK#
        parameter THZ              =     TAC; // tHZ    ps    Data-out high impedance window from CK/CK#
        parameter TDIPW            =    0.35; // tDIPW  tCK   DQ and DM input Pulse Width
        // Data Strobe
        parameter TDQSH            =    0.35; // tDQSH  tCK   DQS input High Pulse Width
        parameter TDQSL            =    0.35; // tDQSL  tCK   DQS input Low Pulse Width
        parameter TDSS             =    0.20; // tDSS   tCK   DQS falling edge to CLK rising (setup time)
        parameter TDSH             =    0.20; // tDSH   tCK   DQS falling edge from CLK rising (hold time)
        parameter TWPRE            =    0.35; // tWPRE  tCK   DQS Write Preamble
        parameter TWPST            =    0.40; // tWPST  tCK   DQS Write Postamble
        parameter TDQSS            =    0.25; // tDQSS  tCK   Rising clock edge to DQS/DQS# latching transition
        // Command and Address
        parameter TIPW             =     0.6; // tIPW   tCK   Control and Address input Pulse Width
        parameter TCCD             =       2; // tCCD   tCK   Cas to Cas command delay
        parameter TRAS_MIN         =   40000; // tRAS   ps    Minimum Active to Precharge command time
        parameter TRAS_MAX         =70000000; // tRAS   ps    Maximum Active to Precharge command time
        parameter TRTP             =    7500; // tRTP   ps    Read to Precharge command delay
        parameter TWR              =   15000; // tWR    ps    Write recovery time
        parameter TMRD             =       2; // tMRD   tCK   Load Mode Register command cycle time
        parameter TDLLK            =     200; // tDLLK  tCK   DLL locking time
        // Refresh
        parameter TRFC_MIN         =  105000; // tRFC   ps    Refresh to Refresh Command interval minimum value
        parameter TRFC_MAX         =70000000; // tRFC   ps    Refresh to Refresh Command Interval maximum value
        // Self Refresh
        parameter TXSNR   = TRFC_MIN + 10000; // tXSNR  ps    Exit self refesh to a non-read command
        parameter TXSRD            =     200; // tXSRD  tCK   Exit self refresh to a read command
        parameter TISXR            =     TIS; // tISXR  ps    CKE setup time during self refresh exit.
        // ODT
        parameter TAOND            =       2; // tAOND  tCK   ODT turn-on delay
        parameter TAOFD            =     2.5; // tAOFD  tCK   ODT turn-off delay
        parameter TAONPD           =    2000; // tAONPD ps    ODT turn-on (precharge power-down mode)
        parameter TAOFPD           =    2000; // tAOFPD ps    ODT turn-off (precharge power-down mode)
        parameter TMOD             =   12000; // tMOD   ps    ODT enable in EMR to ODT pin transition
        // Power Down
        parameter TCKE             =       3; // tCKE   tCK   CKE minimum high or low pulse width

        // Size Parameters based on Part Width

    `ifdef x4
        parameter ADDR_BITS        =      14; // Address Bits
        parameter ROW_BITS         =      14; // Number of Address bits
        parameter COL_BITS         =      11; // Number of Column bits
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter DQ_BITS          =       4; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else `ifdef x8
        parameter ADDR_BITS        =      14; // Address Bits
        parameter ROW_BITS         =      14; // Number of Address bits
        parameter COL_BITS         =      10; // Number of Column bits
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter DQ_BITS          =       8; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else //`define x16
        parameter ADDR_BITS        =      13; // Address Bits
        parameter ROW_BITS         =      13; // Number of Address bits
        parameter COL_BITS         =      10; // Number of Column bits
        parameter DM_BITS          =       2; // Number of Data Mask bits
        parameter DQ_BITS          =      16; // Number of Data bits
        parameter DQS_BITS         =       2; // Number of Dqs bits
        parameter TRRD             =   10000; // tRRD   Active bank a to Active bank b command time
    `endif `endif

    `ifdef QUAD_RANK
        `define DUAL_RANK // also define DUAL_RANK
        parameter CS_BITS          =       4; // Number of Chip Select Bits
        parameter RANKS            =       4; // Number of Chip Select Bits
    `else `ifdef DUAL_RANK
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       2; // Number of Chip Select Bits
    `else
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       1; // Number of Chip Select Bits
    `endif `endif

        // Size Parameters
        parameter BA_BITS          =       2; // Set this parmaeter to control how many Bank Address bits
        parameter MEM_BITS         =      15; // Number of write data bursts can be stored in memory.  The default is 2^10=1024.
        parameter AP               =      10; // the address bit that controls auto-precharge and precharge-all
        parameter BL_BITS          =       3; // the number of bits required to count to MAX_BL
        parameter BO_BITS          =       2; // the number of Burst Order Bits

`else `ifdef x1Gb

    `ifdef sg187E
        parameter TCK_MIN          =    1875; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =      90; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =      75; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     180; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     132; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     157; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     175; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     188; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     250; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     425; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     250; // tQHS   ps    Data hold skew factor
        parameter TAC              =     350; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =       0; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =      75; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     300; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     175; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     125; // tIS    ps    Input Setup Time
        parameter TIH              =     200; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   13125; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   13125; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =      10; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       3; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       3; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       4; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      11; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   13125; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25E
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12500; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12500; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12500; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   17500; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3E
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   18000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg37E
        parameter TCK_MIN          =    3750; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     400; // tQHS   ps    Data hold skew factor
        parameter TAC              =     500; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     225; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     450; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     300; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     250; // tIS    ps    Input Setup Time
        parameter TIH              =     375; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   18750; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else //`define sg5E
        parameter TCK_MIN          =    5000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     150; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     450; // tQHS   ps    Data hold skew factor
        parameter TAC              =     600; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     150; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     275; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     500; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     350; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     350; // tIS    ps    Input Setup Time
        parameter TIH              =     475; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =   10000; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   20000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `endif `endif `endif `endif `endif `endif

    `ifdef x16
      `ifdef sg187E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   50000; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `else // x4, x8
      `ifdef sg187E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   37500; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `endif

        // Timing Parameters

        // Mode Register
        parameter AL_MIN           =       0; // AL     tCK   Minimum Additive Latency
        parameter AL_MAX           =       6; // AL     tCK   Maximum Additive Latency
        parameter CL_MIN           =       3; // CL     tCK   Minimum CAS Latency
        parameter CL_MAX           =       7; // CL     tCK   Maximum CAS Latency
        parameter WR_MIN           =       2; // WR     tCK   Minimum Write Recovery
        parameter WR_MAX           =       8; // WR     tCK   Maximum Write Recovery
        parameter BL_MIN           =       4; // BL     tCK   Minimum Burst Length
        parameter BL_MAX           =       8; // BL     tCK   Minimum Burst Length
        // Clock
        parameter TCK_MAX          =    8000; // tCK    ps    Maximum Clock Cycle Time
        parameter TCH_MIN          =    0.48; // tCH    tCK   Minimum Clock High-Level Pulse Width
        parameter TCH_MAX          =    0.52; // tCH    tCK   Maximum Clock High-Level Pulse Width
        parameter TCL_MIN          =    0.48; // tCL    tCK   Minimum Clock Low-Level Pulse Width
        parameter TCL_MAX          =    0.52; // tCL    tCK   Maximum Clock Low-Level Pulse Width
        // Data
        parameter TLZ              =     TAC; // tLZ    ps    Data-out low-impedance window from CK/CK#
        parameter THZ              =     TAC; // tHZ    ps    Data-out high impedance window from CK/CK#
        parameter TDIPW            =    0.35; // tDIPW  tCK   DQ and DM input Pulse Width
        // Data Strobe
        parameter TDQSH            =    0.35; // tDQSH  tCK   DQS input High Pulse Width
        parameter TDQSL            =    0.35; // tDQSL  tCK   DQS input Low Pulse Width
        parameter TDSS             =    0.20; // tDSS   tCK   DQS falling edge to CLK rising (setup time)
        parameter TDSH             =    0.20; // tDSH   tCK   DQS falling edge from CLK rising (hold time)
        parameter TWPRE            =    0.35; // tWPRE  tCK   DQS Write Preamble
        parameter TWPST            =    0.40; // tWPST  tCK   DQS Write Postamble
        parameter TDQSS            =    0.25; // tDQSS  tCK   Rising clock edge to DQS/DQS# latching transition
        // Command and Address
        parameter TIPW             =     0.6; // tIPW   tCK   Control and Address input Pulse Width
        parameter TCCD             =       2; // tCCD   tCK   Cas to Cas command delay
        parameter TRAS_MIN         =   40000; // tRAS   ps    Minimum Active to Precharge command time
        parameter TRAS_MAX         =70000000; // tRAS   ps    Maximum Active to Precharge command time
        parameter TRTP             =    7500; // tRTP   ps    Read to Precharge command delay
        parameter TWR              =   15000; // tWR    ps    Write recovery time
        parameter TMRD             =       2; // tMRD   tCK   Load Mode Register command cycle time
        parameter TDLLK            =     200; // tDLLK  tCK   DLL locking time
        // Refresh
        parameter TRFC_MIN         =  127500; // tRFC   ps    Refresh to Refresh Command interval minimum value
        parameter TRFC_MAX         =70000000; // tRFC   ps    Refresh to Refresh Command Interval maximum value
        // Self Refresh
        parameter TXSNR   = TRFC_MIN + 10000; // tXSNR  ps    Exit self refesh to a non-read command
        parameter TXSRD            =     200; // tXSRD  tCK   Exit self refresh to a read command
        parameter TISXR            =     TIS; // tISXR  ps    CKE setup time during self refresh exit.
        // ODT
        parameter TAOND            =       2; // tAOND  tCK   ODT turn-on delay
        parameter TAOFD            =     2.5; // tAOFD  tCK   ODT turn-off delay
        parameter TAONPD           =    2000; // tAONPD ps    ODT turn-on (precharge power-down mode)
        parameter TAOFPD           =    2000; // tAOFPD ps    ODT turn-off (precharge power-down mode)
        parameter TMOD             =   12000; // tMOD   ps    ODT enable in EMR to ODT pin transition
        // Power Down
        parameter TCKE             =       3; // tCKE   tCK   CKE minimum high or low pulse width

        // Size Parameters based on Part Width

    `ifdef x4
        parameter ADDR_BITS        =      14; // Address Bits
        parameter ROW_BITS         =      14; // Number of Address bits
        parameter COL_BITS         =      11; // Number of Column bits
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter DQ_BITS          =       4; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else `ifdef x8
        parameter ADDR_BITS        =      14; // Address Bits
        parameter ROW_BITS         =      14; // Number of Address bits
        parameter COL_BITS         =      10; // Number of Column bits
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter DQ_BITS          =       8; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else //`define x16
        parameter ADDR_BITS        =      13; // Address Bits
        parameter ROW_BITS         =      13; // Number of Address bits
        parameter COL_BITS         =      10; // Number of Column bits
        parameter DM_BITS          =       2; // Number of Data Mask bits
        parameter DQ_BITS          =      16; // Number of Data bits
        parameter DQS_BITS         =       2; // Number of Dqs bits
        parameter TRRD             =   10000; // tRRD   Active bank a to Active bank b command time
    `endif `endif

    `ifdef QUAD_RANK
        `define DUAL_RANK // also define DUAL_RANK
        parameter CS_BITS          =       4; // Number of Chip Select Bits
        parameter RANKS            =       4; // Number of Chip Select Bits
    `else `ifdef DUAL_RANK
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       2; // Number of Chip Select Bits
    `else
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       1; // Number of Chip Select Bits
    `endif `endif

        // Size Parameters
        parameter BA_BITS          =       3; // Set this parmaeter to control how many Bank Address bits
        parameter MEM_BITS         =      15; // Number of write data bursts can be stored in memory.  The default is 2^10=1024.
        parameter AP               =      10; // the address bit that controls auto-precharge and precharge-all
        parameter BL_BITS          =       3; // the number of bits required to count to MAX_BL
        parameter BO_BITS          =       2; // the number of Burst Order Bits

`else //`define x2Gb

    `ifdef sg187E
        parameter TCK_MIN          =    1875; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =      90; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =      75; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     180; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     132; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     157; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     175; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     188; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     250; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     425; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     250; // tQHS   ps    Data hold skew factor
        parameter TAC              =     350; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =       0; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =      75; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     300; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     175; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     125; // tIS    ps    Input Setup Time
        parameter TIH              =     200; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   13125; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   13125; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =      10; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       3; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       3; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       4; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      11; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   13125; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25E
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12500; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12500; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12500; // CL     ps    Minimum CAS Latency
    `else `ifdef sg25
        parameter TCK_MIN          =    2500; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     100; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     100; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     200; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     150; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     175; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     200; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     200; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     300; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     300; // tQHS   ps    Data hold skew factor
        parameter TAC              =     400; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =      50; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     125; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     350; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     200; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     175; // tIS    ps    Input Setup Time
        parameter TIH              =     250; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   17500; // tRPA   ps    Precharge All period
        parameter TXARDS           =       8; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =      10; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3E
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   54000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   12000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   12000; // tRP    ps    Precharge command period
        parameter TRPA             =   15000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   12000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg3
        parameter TCK_MIN          =    3000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     340; // tQHS   ps    Data hold skew factor
        parameter TAC              =     450; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     175; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     400; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     240; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     200; // tIS    ps    Input Setup Time
        parameter TIH              =     275; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   18000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       7; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else `ifdef sg37E
        parameter TCK_MIN          =    3750; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     125; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     400; // tQHS   ps    Data hold skew factor
        parameter TAC              =     500; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     100; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     225; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     450; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     300; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     250; // tIS    ps    Input Setup Time
        parameter TIH              =     375; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =    7500; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   18750; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `else //`define sg5E
        parameter TCK_MIN          =    5000; // tCK    ps    Minimum Clock Cycle Time
        parameter TJIT_PER         =     125; // tJIT(per)  ps Period JItter
        parameter TJIT_DUTY        =     150; // tJIT(duty) ps Half Period Jitter
        parameter TJIT_CC          =     250; // tJIT(cc)   ps Cycle to Cycle jitter
        parameter TERR_2PER        =     175; // tERR(nper) ps Accumulated Error (2-cycle)
        parameter TERR_3PER        =     225; // tERR(nper) ps Accumulated Error (3-cycle)
        parameter TERR_4PER        =     250; // tERR(nper) ps Accumulated Error (4-cycle)
        parameter TERR_5PER        =     250; // tERR(nper) ps Accumulated Error (5-cycle)
        parameter TERR_N1PER       =     350; // tERR(nper) ps Accumulated Error (6-10-cycle)
        parameter TERR_N2PER       =     450; // tERR(nper) ps Accumulated Error (11-50-cycle)
        parameter TQHS             =     450; // tQHS   ps    Data hold skew factor
        parameter TAC              =     600; // tAC    ps    DQ output access time from CK/CK#
        parameter TDS              =     150; // tDS    ps    DQ and DM input setup time relative to DQS
        parameter TDH              =     275; // tDH    ps    DQ and DM input hold time relative to DQS
        parameter TDQSCK           =     500; // tDQSCK ps    DQS output access time from CK/CK#
        parameter TDQSQ            =     350; // tDQSQ  ps    DQS-DQ skew, DQS to last DQ valid, per group, per access
        parameter TIS              =     350; // tIS    ps    Input Setup Time
        parameter TIH              =     475; // tIH    ps    Input Hold Time
        parameter TRC              =   55000; // tRC    ps    Active to Active/Auto Refresh command time
        parameter TRCD             =   15000; // tRCD   ps    Active to Read/Write command time
        parameter TWTR             =   10000; // tWTR   ps    Write to Read command delay
        parameter TRP              =   15000; // tRP    ps    Precharge command period
        parameter TRPA             =   20000; // tRPA   ps    Precharge All period
        parameter TXARDS           =       6; // tXARDS tCK   Exit low power active power down to a read command
        parameter TXARD            =       2; // tXARD  tCK   Exit active power down to a read command
        parameter TXP              =       2; // tXP    tCK   Exit power down to a non-read command
        parameter TANPD            =       3; // tANPD  tCK   ODT to power-down entry latency
        parameter TAXPD            =       8; // tAXPD  tCK   ODT power-down exit latency
        parameter CL_TIME          =   15000; // CL     ps    Minimum CAS Latency
    `endif `endif `endif `endif `endif `endif

    `ifdef x16
      `ifdef sg187E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   45000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   50000; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `else // x4, x8
      `ifdef sg187E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25E
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else `ifdef sg25
        parameter TFAW             =   35000; // tFAW  ps     Four Bank Activate window
      `else // sg3E, sg3, sg37E, sg5E
        parameter TFAW             =   37500; // tFAW  ps     Four Bank Activate window
      `endif `endif `endif
    `endif

        // Timing Parameters

        // Mode Register
        parameter AL_MIN           =       0; // AL     tCK   Minimum Additive Latency
        parameter AL_MAX           =       6; // AL     tCK   Maximum Additive Latency
        parameter CL_MIN           =       3; // CL     tCK   Minimum CAS Latency
        parameter CL_MAX           =       7; // CL     tCK   Maximum CAS Latency
        parameter WR_MIN           =       2; // WR     tCK   Minimum Write Recovery
        parameter WR_MAX           =       8; // WR     tCK   Maximum Write Recovery
        parameter BL_MIN           =       4; // BL     tCK   Minimum Burst Length
        parameter BL_MAX           =       8; // BL     tCK   Minimum Burst Length
        // Clock
        parameter TCK_MAX          =    8000; // tCK    ps    Maximum Clock Cycle Time
        parameter TCH_MIN          =    0.48; // tCH    tCK   Minimum Clock High-Level Pulse Width
        parameter TCH_MAX          =    0.52; // tCH    tCK   Maximum Clock High-Level Pulse Width
        parameter TCL_MIN          =    0.48; // tCL    tCK   Minimum Clock Low-Level Pulse Width
        parameter TCL_MAX          =    0.52; // tCL    tCK   Maximum Clock Low-Level Pulse Width
        // Data
        parameter TLZ              =     TAC; // tLZ    ps    Data-out low-impedance window from CK/CK#
        parameter THZ              =     TAC; // tHZ    ps    Data-out high impedance window from CK/CK#
        parameter TDIPW            =    0.35; // tDIPW  tCK   DQ and DM input Pulse Width
        // Data Strobe
        parameter TDQSH            =    0.35; // tDQSH  tCK   DQS input High Pulse Width
        parameter TDQSL            =    0.35; // tDQSL  tCK   DQS input Low Pulse Width
        parameter TDSS             =    0.20; // tDSS   tCK   DQS falling edge to CLK rising (setup time)
        parameter TDSH             =    0.20; // tDSH   tCK   DQS falling edge from CLK rising (hold time)
        parameter TWPRE            =    0.35; // tWPRE  tCK   DQS Write Preamble
        parameter TWPST            =    0.40; // tWPST  tCK   DQS Write Postamble
        parameter TDQSS            =    0.25; // tDQSS  tCK   Rising clock edge to DQS/DQS# latching transition
        // Command and Address
        parameter TIPW             =     0.6; // tIPW   tCK   Control and Address input Pulse Width
        parameter TCCD             =       2; // tCCD   tCK   Cas to Cas command delay
        parameter TRAS_MIN         =   40000; // tRAS   ps    Minimum Active to Precharge command time
        parameter TRAS_MAX         =70000000; // tRAS   ps    Maximum Active to Precharge command time
        parameter TRTP             =    7500; // tRTP   ps    Read to Precharge command delay
        parameter TWR              =   15000; // tWR    ps    Write recovery time
        parameter TMRD             =       2; // tMRD   tCK   Load Mode Register command cycle time
        parameter TDLLK            =     200; // tDLLK  tCK   DLL locking time
        // Refresh
        parameter TRFC_MIN         =  197500; // tRFC   ps    Refresh to Refresh Command interval minimum value
        parameter TRFC_MAX         =70000000; // tRFC   ps    Refresh to Refresh Command Interval maximum value
        // Self Refresh
        parameter TXSNR   = TRFC_MIN + 10000; // tXSNR  ps    Exit self refesh to a non-read command
        parameter TXSRD            =     200; // tXSRD  tCK   Exit self refresh to a read command
        parameter TISXR            =     TIS; // tISXR  ps    CKE setup time during self refresh exit.
        // ODT
        parameter TAOND            =       2; // tAOND  tCK   ODT turn-on delay
        parameter TAOFD            =     2.5; // tAOFD  tCK   ODT turn-off delay
        parameter TAONPD           =    2000; // tAONPD ps    ODT turn-on (precharge power-down mode)
        parameter TAOFPD           =    2000; // tAOFPD ps    ODT turn-off (precharge power-down mode)
        parameter TMOD             =   12000; // tMOD   ps    ODT enable in EMR to ODT pin transition
        // Power Down
        parameter TCKE             =       3; // tCKE   tCK   CKE minimum high or low pulse width

        // Size Parameters based on Part Width

    `ifdef x4
        parameter ADDR_BITS        =      15; // Address Bits
        parameter ROW_BITS         =      15; // Number of Address bits
        parameter COL_BITS         =      11; // Number of Column bits
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter DQ_BITS          =       4; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else `ifdef x8
        parameter ADDR_BITS        =      15; // Address Bits
        parameter ROW_BITS         =      15; // Number of Address bits
        parameter COL_BITS         =      10; // Number of Column bits
        parameter DM_BITS          =       1; // Number of Data Mask bits
        parameter DQ_BITS          =       8; // Number of Data bits
        parameter DQS_BITS         =       1; // Number of Dqs bits
        parameter TRRD             =    7500; // tRRD   Active bank a to Active bank b command time
    `else //`define x16
        parameter ADDR_BITS        =      14; // Address Bits
        parameter ROW_BITS         =      14; // Number of Address bits
        parameter COL_BITS         =      10; // Number of Column bits
        parameter DM_BITS          =       2; // Number of Data Mask bits
        parameter DQ_BITS          =      16; // Number of Data bits
        parameter DQS_BITS         =       2; // Number of Dqs bits
        parameter TRRD             =   10000; // tRRD   Active bank a to Active bank b command time
    `endif `endif

    `ifdef QUAD_RANK
        `define DUAL_RANK // also define DUAL_RANK
        parameter CS_BITS          =       4; // Number of Chip Select Bits
        parameter RANKS            =       4; // Number of Chip Select Bits
    `else `ifdef DUAL_RANK
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       2; // Number of Chip Select Bits
    `else
        parameter CS_BITS          =       2; // Number of Chip Select Bits
        parameter RANKS            =       1; // Number of Chip Select Bits
    `endif `endif

        // Size Parameters
        parameter BA_BITS          =       3; // Set this parmaeter to control how many Bank Address bits
        parameter MEM_BITS         =      15; // Number of write data bursts can be stored in memory.  The default is 2^10=1024.
        parameter AP               =      10; // the address bit that controls auto-precharge and precharge-all
        parameter BL_BITS          =       3; // the number of bits required to count to MAX_BL
        parameter BO_BITS          =       2; // the number of Burst Order Bits

`endif `endif `endif

    // Simulation parameters
    parameter STOP_ON_ERROR    =       1; // If set to 1, the model will halt on command sequence/major errors
    parameter DEBUG            =       1; // Turn on Debug messages
    parameter BUS_DELAY        =       0; // delay in nanoseconds
    parameter RANDOM_OUT_DELAY =       0; // If set to 1, the model will put a random amount of delay on DQ/DQS during reads
    parameter RANDOM_SEED      = 711689044; //seed value for random generator.

    parameter RDQSEN_PRE       =       2; // DQS driving time prior to first read strobe
    parameter RDQSEN_PST       =       1; // DQS driving time after last read strobe
    parameter RDQS_PRE         =       2; // DQS low time prior to first read strobe
    parameter RDQS_PST         =       1; // DQS low time after last valid read strobe
    parameter RDQEN_PRE        =       0; // DQ/DM driving time prior to first read data
    parameter RDQEN_PST        =       0; // DQ/DM driving time after last read data
    parameter WDQS_PRE         =       1; // DQS half clock periods prior to first write strobe
    parameter WDQS_PST         =       1; // DQS half clock periods after last valid write strobe
