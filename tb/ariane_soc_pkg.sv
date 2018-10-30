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

    localparam NB_PERIPHERALS = 7;
    localparam NumTargets = 2;
    localparam NumSources = 2;

    typedef enum int unsigned {
        DRAM  = 0,
        SPI   = 1,
        UART  = 2,
        PLIC  = 3,
        CLINT = 4,
        ROM   = 5,
        Debug = 6

    } axi_slaves_t;

    typedef enum logic [63:0] {
        DebugBase = 64'h0000_0000,
        ROMBase   = 64'h0001_0000,
        CLINTBase = 64'h0200_0000,
        PLICBase  = 64'h0C00_0000,
        UARTBase  = 64'h1000_0000,
        SPIBase   = 64'h2000_0000,
        DRAMBase  = 64'h8000_0000
    } soc_bus_start_t;

    localparam logic[63:0] DebugLength = 64'h1000;
    localparam logic[63:0] ROMLength   = 64'h1000;
    localparam logic[63:0] CLINTLength = 64'hC0000;
    localparam logic[63:0] PLICLength  = 64'h3FF_FFFF;
    localparam logic[63:0] UARTLength  = 64'h10000;
    localparam logic[63:0] SPILength   = 64'h1000;
    localparam logic[63:0] DRAMLength  = 64'h4000000;
endpackage