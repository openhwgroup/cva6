// SPDX-License-Identifier: Apache-2.0
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

#include "Vecc_encode.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "ecc.h"

#include <stdio.h>
#include <assert.h>

// #define DEBUG 1
// This is a 64-bit integer to reduce wrap over issues and
// allow modulus.  You can also use a double, if you wish.
vluint64_t main_time = 0;

// Called by $time in Verilog
// converts to double, to match
// what SystemC does
double sc_time_stamp () {
    return main_time;
}

int main(int argc, char** argv, char** env) {

    Verilated::commandArgs(argc, argv);
    Vecc_encode* dut = new Vecc_encode;

    int d = 64; // code word length
    int p = calcParityLen(d);  // parity length

    // input word
    uint64_t word = 0x55555555;
    // allocate 8 bit per byt
    uint8_t info [d];
    uint8_t parity [d];
    uint8_t codeword [d + p + 1];

    Verilated::traceEverOn(true);
    VerilatedVcdC* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);  // Trace 99 levels of hierarchy
    tfp->open("ecc_encode.vcd");

    while (!Verilated::gotFinish()) {
        // Set Input
        dut->data_i = word;

        ecc_encode(word, d, codeword);

        // Eval DUT
        dut->eval();

        // Read Output
        // Check - Output
        for (int i = 0; i < 3; i++){
            toBin(info, dut->data_o[i], 32);
            // check each bit
            for (int j = 0; j < 32; j++) {
                // printf("%d ", j);
                if (j + i*32 < d + p + 1) assert(info[j] == codeword[j + i*32]);
            }
        }
        // Advance Time
        main_time++;

        word = random() << 32 | random();

        tfp->dump(main_time);

        if (main_time > 100000) break;
    }
    dut->final();
    tfp->close();
    delete dut;
    exit(0);
}
