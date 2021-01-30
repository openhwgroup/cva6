///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2021 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
///////////////////////////////////////////////////////////////////////////////
//
// C++ wrapper for the CVA6 testharness - needed for Verilator.
//
///////////////////////////////////////////////////////////////////////////////
#include "svdpi.h"
#include "Vcva6_testharness.h"
#include "verilated_vcd_c.h"
#include "verilated.h"

#include <iostream>
#include <iomanip>
#include <fstream>
#include <exception>
#include <cstdio>
#include <cstdint>
#include <cerrno>

//void dump_memory();
double sc_time_stamp();

static vluint64_t t = 0;
Vcva6_testharness *top;

int main(int argc, char **argv, char **env)
{

    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);
    top = new Vcva6_testharness();

    //svSetScope(svGetScopeFromName(
    //    "TOP.tb_top_verilator.cv32e40p_tb_wrapper_i.ram_i.dp_ram_i"));
    //Verilated::scopesDump();

#ifdef VCD_TRACE
    VerilatedVcdC *tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open("Vcva6_core_tb.vcd");
#endif
    //top->fetch_enable_i = 1;
    top->clk_i          = 0;
    top->rst_ni         = 0;

    top->eval();
    //dump_memory();

    while (!Verilated::gotFinish()) {
        if (t > 40)
            top->rst_ni = 1;
        top->clk_i = !top->clk_i;
        top->eval();
#ifdef VCD_TRACE
        tfp->dump(t);
#endif
        t += 5;
    }
#ifdef VCD_TRACE
    tfp->close();
#endif
    delete top;
    exit(0);
}

double sc_time_stamp()
{
    return t;
}

//TODO: integrate I&D memory into cva6_testharness
/*
void dump_memory()
{
    errno = 0;
    std::ofstream mem_file;
    svLogicVecVal addr = {0};

    mem_file.exceptions(std::ofstream::failbit | std::ofstream::badbit);
    try {
        mem_file.open("memory_dump.bin");
        for (size_t i = 0; i < 1048576; i++) {
            addr.aval    = i;
            uint32_t val = read_byte(&addr);
            //uint32_t val = read_byte(&addr.aval);  // mike@openhwgroup.org: if the above line fails to compile on your system, try this line
            mem_file << std::setfill('0') << std::setw(2) << std::hex << val
                     << std::endl;
        }
        mem_file.close();

        std::cout << "finished dumping memory" << std::endl;

    } catch (std::ofstream::failure e) {
        std::cerr << "exception opening/reading/closing file memory_dump.bin\n";
    }
}
*/
