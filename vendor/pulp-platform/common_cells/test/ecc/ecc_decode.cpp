// SPDX-License-Identifier: Apache-2.0
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

#include "Vecc_decode.h"
#include "verilated.h"
#include "verilated_vcd_c.h"
#include "ecc.h"

#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>

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
    Vecc_decode* dut = new Vecc_decode;

    int d = 64; // code word length
    int p = calcParityLen(d);  // parity length

    // number of bytes to store the codeword
    int cw_byte = (int) ceil((d + p + 1)/32.0);

    // input word
    uint64_t word = 0x55555555;
    uint8_t codeword [d + p + 1];
    // allocate 8 bit per byt
    uint8_t encoded_word [cw_byte];
    uint8_t parity [d];

    uint8_t single_error, parity_error, double_error;

    Verilated::traceEverOn(true);
    VerilatedVcdC* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);  // Trace 99 levels of hierarchy
    tfp->open("ecc_decode.vcd");

    while (!Verilated::gotFinish()) {

        ecc_encode(word, d, codeword);

        for (int i = 0; i < cw_byte; i++) encoded_word[i] = 0;

        toByte(encoded_word, codeword, d + p + 1);

        printf("[DUT] input  = %llx\n", word);
        // Apply Input Data
        for (int i = 0; i < cw_byte; i++) {
            dut->data_i[i] = *((unsigned int *) encoded_word + i);
        }

        // randomly inject some errors
        single_error = 0;
        double_error = 0;
        parity_error = 0;

        switch (random() % 10) {
            // inject single error
            case 0:
                printf("Injecting single error\n");
                single_error = 1;
                dut->data_i[random() % (cw_byte - 1)] ^= 0x1 << (random() % 8);
                break;
            // parity error
            case 1:
                printf("Injecting parity error\n");
                parity_error = 1;
                dut->data_i[cw_byte-1] ^= 0x80;
                break;
            // inject double error
            case 2:
                printf("Injecting double error\n");
                double_error = 1;
                dut->data_i[random() % (cw_byte - 1)] ^= 0x3 << (random() % 8);
                break;
        }

        // Eval DUT
        dut->eval();

        printf("[DUT] output = %lx\n", dut->data_o);
        assert (double_error || dut->data_o == word);
        assert (dut->single_error_o == single_error);
        assert (dut->parity_error_o == parity_error);
        assert (dut->double_error_o == double_error);
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
