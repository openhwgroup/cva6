/*
 *******************************************************************************
 *
 * Copyright 2021 OpenHW Group
 *
 * Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://solderpad.org/licenses/
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
 *
 *******************************************************************************
 *
 * Verilator top for the CVA6 "core_only" testbench.
 * Genrates clock, reset and optionally dumps waves.
 *
 *******************************************************************************
 */

#include "svdpi.h"
//#include "Vcva6_core_only_tb__Dpi.h"
#include "Vcva6_core_only_tb.h"
#include "verilated_vcd_c.h"
#include "verilated.h"

#include <iostream>
#include <iomanip>
#include <fstream>
#include <exception>
#include <cstdio>
#include <cstdint>
#include <cerrno>

double sc_time_stamp();

static vluint64_t t = 0;
Vcva6_core_only_tb *top;

int main(int argc, char **argv, char **env)
{

    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);
    top = new Vcva6_core_only_tb();

    //svSetScope(svGetScopeFromName(
    //    "TOP.tb_top_verilator.cv32e40p_tb_wrapper_i.ram_i.dp_ram_i"));
    Verilated::scopesDump();

#ifdef VCD_TRACE
    VerilatedVcdC *tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open("verilator_tb.vcd");
#endif
    top->verilator_clk_i  = 0;
    top->verilator_rstn_i = 0;

    top->eval();
    //dump_memory();

    while (!Verilated::gotFinish()) {
        if (t > 40)
            top->verilator_rstn_i = 1;
        top->verilator_clk_i = !top->verilator_clk_i;
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
