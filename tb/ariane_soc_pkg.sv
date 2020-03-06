// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Description: Contains SoC information as constants
package ariane_soc;
  // M-Mode Hart, S-Mode Hart
  localparam int unsigned NumTargets = 2;
  // Uart, SPI, Ethernet, reserved
  localparam int unsigned NumSources = 30;
  localparam int unsigned MaxPriority = 7;

  localparam NrSlaves = 2; // actually masters, but slaves on the crossbar

  // 4 is recommended by AXI standard, so lets stick to it, do not change
  localparam IdWidth   = 4;
  localparam IdWidthSlave = IdWidth + $clog2(NrSlaves);

  typedef enum int unsigned {
    AxiDram      = 0,
    AxiGpio      = 1,
    AxiEthernet  = 2,
    AxiSpi       = 3,
    AxiApbPeriph = 4,
    AxiClint     = 5,
    AxiRom       = 6,
    AxiDebug     = 7
  } ariane_soc_axi_slaves_e;

  localparam int unsigned NoSocAxiSlaves = AxiDebug + 1;

  typedef enum int unsigned {
    ApbTimer = 0,
    ApbUart  = 1,
    ApbPlic  = 2
  } apb_peripherals_e;

  localparam int unsigned NoApbSlaves = ApbPlic + 1;

  // This value because the APB slaves share the AxiApbPeriph port
  localparam int unsigned NoSocAxiAddrRules = AxiDebug + ApbPlic + 1;

  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         NrSlaves,            // # of slave ports, so many masters are connected to the xbar
    NoMstPorts:         NoSocAxiSlaves,      // # of master ports, so many slaves are connected to the xbar
    MaxMstTrans:        8,                   // Maxi # of outstanding transactions per r/w per master
    MaxSlvTrans:        8,                   // Maxi # of outstanding write transactions per slave
    FallThrough:        1'b0,                // AreAW -> W Fifo's in Fall through mode (1'b0 = long paths)
    LatencyMode:        axi_pkg::CUT_ALL_AX, // See xbar_latency_t and get_xbarlatmode
    AxiIdWidthSlvPorts: IdWidth,             // Axi Id Width of the Slave Ports
    AxiIdUsedSlvPorts:  IdWidth,             // this many LSB's of the SlvPortAxiId get used in demux
    AxiAddrWidth:       32'd64,              // Axi Address Width
    AxiDataWidth:       32'd64,              // Axi Data Width
    NoAddrRules:        NoSocAxiAddrRules    // # of Address Rules in the memory map
  };


  localparam logic[63:0] DebugLength    = 64'h1000;
  localparam logic[63:0] ROMLength      = 64'h10000;
  localparam logic[63:0] CLINTLength    = 64'hC0000;
  localparam logic[63:0] PLICLength     = 64'h3FF_FFFF;
  localparam logic[63:0] UARTLength     = 64'h1000;
  localparam logic[63:0] TimerLength    = 64'h1000;
  localparam logic[63:0] SPILength      = 64'h800000;
  localparam logic[63:0] EthernetLength = 64'h10000;
  localparam logic[63:0] GPIOLength     = 64'h1000;
  localparam logic[63:0] DRAMLength     = 64'h40000000; // 1GByte of DDR (split between two chips on Genesys2)
  localparam logic[63:0] SRAMLength     = 64'h1800000;  // 24 MByte of SRAM
  // Instantiate AXI protocol checkers
  localparam bit GenProtocolChecker = 1'b0;

  typedef enum logic [63:0] {
    DebugBase    = 64'h0000_0000,
    ROMBase      = 64'h0001_0000,
    CLINTBase    = 64'h0200_0000,
    PLICBase     = 64'h0C00_0000,
    UARTBase     = 64'h1000_0000,
    TimerBase    = 64'h1800_0000,
    SPIBase      = 64'h2000_0000,
    EthernetBase = 64'h3000_0000,
    GPIOBase     = 64'h4000_0000,
    DRAMBase     = 64'h8000_0000
  } soc_bus_start_t;


  localparam axi_pkg::xbar_rule_64_t [NoSocAxiAddrRules-1:0] AxiAddrMap = '{
    '{idx:        AxiDram,
      start_addr: DRAMBase,
      end_addr:   DRAMBase     + DRAMLength     },
    '{idx:        AxiGpio,
      start_addr: GPIOBase,
      end_addr:   GPIOBase     + GPIOLength     },
    '{idx:        AxiEthernet,
      start_addr: EthernetBase,
      end_addr:   EthernetBase + EthernetLength },
    '{idx:        AxiSpi,
      start_addr: SPIBase,
      end_addr:   SPIBase      + SPILength      },
    '{idx:        AxiApbPeriph,
      start_addr: TimerBase,
      end_addr:   TimerBase    + TimerLength    },
    '{idx:        AxiApbPeriph,
      start_addr: UARTBase,
      end_addr:   UARTBase     + UARTLength     },
    '{idx:        AxiApbPeriph,
      start_addr: PLICBase,
      end_addr:   PLICBase     + PLICLength     },
    '{idx:        AxiClint,
      start_addr: CLINTBase,
      end_addr:   CLINTBase    + CLINTLength    },
    '{idx:        AxiRom,
      start_addr: ROMBase,
      end_addr:   ROMBase      + ROMLength      },
    '{idx:        AxiDebug,
      start_addr: DebugBase,
      end_addr:   DebugBase    + DebugLength    }
  };

  localparam axi_pkg::xbar_rule_64_t [NoApbSlaves-1:0] ApbAddrMap = '{
    '{idx:        ApbTimer,
      start_addr: TimerBase,
      end_addr:   TimerBase    + TimerLength    },
    '{idx:        ApbUart,
      start_addr: UARTBase,
      end_addr:   UARTBase     + UARTLength     },
    '{idx:        ApbPlic,
      start_addr: PLICBase,
      end_addr:   PLICBase     + PLICLength     }
  };

  localparam ariane_pkg::ariane_cfg_t ArianeSocCfg = '{
    RASDepth: 2,
    BTBEntries: 32,
    BHTEntries: 128,
    // idempotent region
    NrNonIdempotentRules:  1,
    NonIdempotentAddrBase: {64'b0},
    NonIdempotentLength:   {DRAMBase},
    NrExecuteRegionRules:  3,
    ExecuteRegionAddrBase: {DRAMBase,   ROMBase,   DebugBase},
    ExecuteRegionLength:   {DRAMLength, ROMLength, DebugLength},
    // cached region
    NrCachedRegionRules:    1,
    CachedRegionAddrBase:  {DRAMBase},
    CachedRegionLength:    {DRAMLength},
    //  cache config
    Axi64BitCompliant:      1'b1,
    SwapEndianess:          1'b0,
    // debug
    DmBaseAddress:          DebugBase
  };

endpackage
