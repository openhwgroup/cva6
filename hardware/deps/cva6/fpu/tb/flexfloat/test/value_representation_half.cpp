/*
   Copyright 2018 - The OPRECOMP Project Consortium, Alma Mater Studiorum
   Università di Bologna. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/


#include <gtest/gtest.h>
#include <flexfloat.hpp>

void show(fp_t d)
{
    #ifdef FLEXFLOAT_ON_QUAD
    char buffer[128];
    quadmath_snprintf(buffer, sizeof buffer, "%.38Qf", d);
    printf("%s\t", buffer);
    #else
    printf(PRINTF_FORMAT "\t", d);
    #endif
    uint_t u = *((uint_t *) &d);
    #ifdef FLEXFLOAT_ON_SINGLE
    printf("0x%016x\t", u);
    #endif
    #ifdef FLEXFLOAT_ON_DOUBLE
    printf("0x%016lx\t", u);
    #endif    
    std::cout << std::bitset<NUM_BITS>(u) << std::endl;
}

class MyTest
    : public ::testing::TestWithParam<std::tuple<uint64_t, uint64_t>> {
};

TEST_P(MyTest, TestFormula)
{
    uint64_t const in_number = std::get<0>(GetParam());
    uint64_t const out_number = std::get<1>(GetParam());

    fp_t d = reinterpret_double_bits_as(in_number);
    fp_t expected = reinterpret_double_bits_as(out_number);

    // IEEE half.
    flexfloat<5, 10> fx = d;
    fp_t recoverd_fx = (fp_t)(fx);

     //printf("number:     \t"); show(d);
     //printf("recoverd_fx:\t"); show(recoverd_fx);
     //printf("expected:   \t"); show(expected);

    // Enforces the same reprsentation for nan's.
    uint_t out = reinterpret_as_double_bits(recoverd_fx);

    #ifndef FLEXFLOAT_ON_SINGLE
    #ifdef FLEXFLOAT_ROUNDING
    ASSERT_EQ(out, out_number);
    #endif
    #endif
    // ASSERT_EQ(recoverd_fx, expected); // does not work for NAN's.
}

INSTANTIATE_TEST_CASE_P(
    TestWithParameters_manual_sampels, MyTest,
    testing::Values(

        // Case triggering >> 64 (does generates wrong masks)
        // number:     	6.09397888183593736447e-05	0x3f0ff33333333333
        // 0011111100001111111100110011001100110011001100110011001100110011
        // recoverd_sf:	6.09159469604492187500e-05	0x3f0ff00000000000
        // 0011111100001111111100000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3f0ff33333333333, 0x3f0ff00000000000),

        // Case, triggering rounding twice after each other not the same ase
        // rounding once (sticky bit)
        // number:     	6.09517097473144544803e-05	0x3f0ff4cccccccccd
        // 0011111100001111111101001100110011001100110011001100110011001101
        // recoverd_sf:	6.09755516052246093750e-05	0x3f0ff80000000000
        // 0011111100001111111110000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3f0ff4cccccccccd, 0x3f0ff80000000000),

        // Case that triggers a MANTISSA overflow due rounding, requires the
        // exponent to be changed.
        // number:     	3.05056571960449225526e-05	0x3efffccccccccccd
        // 0011111011111111111111001100110011001100110011001100110011001101
        // recoverd_sf:	3.05175781250000000000e-05	0x3f00000000000000
        // 0011111100000000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3efffccccccccccd, 0x3f00000000000000),

        // Super ugly (and rare) case! A very small sub-normal number requires
        // the mantissa bits almost to be moved out of the storage range.
        // Henceforth, the correct rounding should go either up / or down. In
        // that case, the rounding depends on the hidden 1, not explicitly
        // stored in the mantissa. (BUGFIX) add the hidden one, perform correct
        // rounding and go furhter in the routine. That requires to change the
        // exponent due rounding at a later point.
        // number:     	4.76837158203125026470e-08	0x3e6999999999999a
        // 0011111001101001100110011001100110011001100110011001100110011010
        // recoverd_sf:	5.96046447753906250000e-08	0x3e70000000000000
        // 0011111001110000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3e6999999999999a, 0x3e70000000000000),

        // A number smaller than the smallest subnormal, requires a full flush
        // to 0.
        // number:     	2.38418579101562513235e-08	0x3e5999999999999a
        // 0011111001011001100110011001100110011001100110011001100110011010
        // recoverd_sf:	0.00000000000000000000e+00	0x0000000000000000
        // 0000000000000000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3e5999999999999a, 0x0000000000000000)));


INSTANTIATE_TEST_CASE_P(
    // Cases showing failuers during a float - Half - float brute force test!
    TestWithParameters_manual_sampels_002, MyTest,
    testing::Values(
        // number:     	1.58346726468704329014e-43	0x370c400000000000
        // 0011011100001100010000000000000000000000000000000000000000000000
        // recoverd_sf:	0.00000000000000000000e+00	0x0000000000000000
        // 0000000000000000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x370c400000000000, 0x0000000000000000),
        // number:     	4.88279038108885288239e-04	0x3f3ffff680000000
        // 0011111100111111111111111111011010000000000000000000000000000000
        // recoverd_sf:	4.88281250000000000000e-04	0x3f40000000000000
        // 0011111101000000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3f3ffff680000000, 0x3f40000000000000),
        // number:     	6.60882968750000000000e+04	0x40f02284c0000000
        // 0100000011110000001000101000010011000000000000000000000000000000
        // recoverd_sf:	inf	0x7ff0000000000000
        // 0111111111110000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x40f02284c0000000, 0x7ff0000000000000),
        // number:     	nan	0x7ff80e1780000000
        // 0111111111111000000011100001011110000000000000000000000000000000
        // recoverd_sf:	nan	0x7ff80c0000000000
        // 0111111111111000000011000000000000000000000000000000000000000000
        ::testing::make_tuple(0x7ff80e1780000000, 0x7ff80c0000000000),
        // number:     	nan	0x7ff80eeeeeeeeeee
        // 0111111111111000000011101110111011101110111011101110111011101110
        // recoverd_sf:	nan	0x7ff80c0000000000
        // 0111111111111000000011000000000000000000000000000000000000000000
        ::testing::make_tuple(0x7ff80eeeeeeeeeee, 0x7ff80c0000000000),
        // number:     	-2.98454239100465201773e-08	0xbe6005ec80000000
        // 1011111001100000000001011110110010000000000000000000000000000000
        // recoverd_sf:	-5.96046447753906250000e-08	0xbe70000000000000
        // 1011111001110000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0xbe6005ec80000000, 0xbe70000000000000)));


INSTANTIATE_TEST_CASE_P(
    TestWithParametersC1, MyTest,
    testing::Values(
        // number:     	1.00000000000000000000e+00	0x3ff0000000000000
        // 0011111111110000000000000000000000000000000000000000000000000000
        // recoverd_sf:	1.00000000000000000000e+00	0x3ff0000000000000
        // 0011111111110000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3ff0000000000000, 0x3ff0000000000000),
        // number:     	5.00000000000000000000e-01	0x3fe0000000000000
        // 0011111111100000000000000000000000000000000000000000000000000000
        // recoverd_sf:	5.00000000000000000000e-01	0x3fe0000000000000
        // 0011111111100000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fe0000000000000, 0x3fe0000000000000),
        // number:     	3.33333333333333314830e-01	0x3fd5555555555555
        // 0011111111010101010101010101010101010101010101010101010101010101
        // recoverd_sf:	3.33251953125000000000e-01	0x3fd5540000000000
        // 0011111111010101010101000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fd5555555555555, 0x3fd5540000000000),
        // number:     	2.50000000000000000000e-01	0x3fd0000000000000
        // 0011111111010000000000000000000000000000000000000000000000000000
        // recoverd_sf:	2.50000000000000000000e-01	0x3fd0000000000000
        // 0011111111010000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fd0000000000000, 0x3fd0000000000000),
        // number:     	2.00000000000000011102e-01	0x3fc999999999999a
        // 0011111111001001100110011001100110011001100110011001100110011010
        // recoverd_sf:	1.99951171875000000000e-01	0x3fc9980000000000
        // 0011111111001001100110000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fc999999999999a, 0x3fc9980000000000),
        // number:     	1.66666666666666657415e-01	0x3fc5555555555555
        // 0011111111000101010101010101010101010101010101010101010101010101
        // recoverd_sf:	1.66625976562500000000e-01	0x3fc5540000000000
        // 0011111111000101010101000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fc5555555555555, 0x3fc5540000000000),
        // number:     	1.42857142857142849213e-01	0x3fc2492492492492
        // 0011111111000010010010010010010010010010010010010010010010010010
        // recoverd_sf:	1.42822265625000000000e-01	0x3fc2480000000000
        // 0011111111000010010010000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fc2492492492492, 0x3fc2480000000000),
        // number:     	1.25000000000000000000e-01	0x3fc0000000000000
        // 0011111111000000000000000000000000000000000000000000000000000000
        // recoverd_sf:	1.25000000000000000000e-01	0x3fc0000000000000
        // 0011111111000000000000000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fc0000000000000, 0x3fc0000000000000),
        // number:     	1.11111111111111104943e-01	0x3fbc71c71c71c71c
        // 0011111110111100011100011100011100011100011100011100011100011100
        // recoverd_sf:	1.11083984375000000000e-01	0x3fbc700000000000
        // 0011111110111100011100000000000000000000000000000000000000000000
        ::testing::make_tuple(0x3fbc71c71c71c71c, 0x3fbc700000000000)));

// Brute force snippsets from extracted from softlow
INSTANTIATE_TEST_CASE_P(
    TestWithParameters_BF_001, MyTest,
    testing::Values(
        // start: 0
        // stop:  50
        // inc:   1
        ::testing::make_tuple(0x0000000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36a0000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36b0000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36b8000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36c0000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36c4000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36c8000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36cc000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36d0000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36d2000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36d4000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36d6000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36d8000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36da000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36dc000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36de000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e0000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e1000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e2000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e3000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e4000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e5000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e6000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e7000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e8000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36e9000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36ea000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36eb000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36ec000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36ed000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36ee000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36ef000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f0000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f0800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f1000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f1800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f2000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f2800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f3000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f3800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f4000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f4800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f5000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f5800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f6000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f6800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f7000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f7800000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f8000000000000, 0x0000000000000000),
        ::testing::make_tuple(0x36f8800000000000, 0x0000000000000000)));

INSTANTIATE_TEST_CASE_P(
    TestWithParameters_BF_002, MyTest,
    testing::Values(
        // start: 97495757619
        // stop:  97495757669
        // inc:   1
        ::testing::make_tuple(0xbe66666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666680000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666666a0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666666c0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666666e0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666700000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666720000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666740000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666760000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666780000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666667a0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666667c0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666667e0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666800000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666820000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666840000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666860000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666880000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666668a0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666668c0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666668e0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666900000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666920000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666940000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666960000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666980000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666669a0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666669c0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe666669e0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666a00000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666a20000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666a40000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666a60000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666a80000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666aa0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666ac0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666ae0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666b00000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666b20000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666b40000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666b60000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666b80000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666ba0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666bc0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666be0000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666c00000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666c20000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666c40000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666c60000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe66666c80000000, 0xbe70000000000000)));

INSTANTIATE_TEST_CASE_P(
    TestWithParameters_BF_003, MyTest,
    testing::Values(
        // start: 214318868070
        // stop:  214318868120
        // inc:   1
        ::testing::make_tuple(0xc4ccccccc0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccce0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccd00000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccd20000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccd40000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccd60000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccd80000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccda0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccdc0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccde0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccce00000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccce20000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccce40000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccce60000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccce80000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccea0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccec0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccee0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccf00000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccf20000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccf40000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccf60000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccf80000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccfa0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccfc0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4cccccfe0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd000000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd020000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd040000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd060000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd080000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd0a0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd0c0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd0e0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd100000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd120000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd140000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd160000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd180000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd1a0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd1c0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd1e0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd200000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd220000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd240000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd260000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd280000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd2a0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd2c0000000, 0xfff0000000000000),
        ::testing::make_tuple(0xc4ccccd2e0000000, 0xfff0000000000000)));

INSTANTIATE_TEST_CASE_P(
    TestWithParameters_BF_004, MyTest,
    testing::Values(
        // start: 429492434632
        // stop:  429492434682
        // inc:   1
        ::testing::make_tuple(0xffffced900000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffced920000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffced940000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffced960000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffced980000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffced9a0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffced9c0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffced9e0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffceda00000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffceda20000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffceda40000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffceda60000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffceda80000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedaa0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedac0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedae0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedb00000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedb20000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedb40000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedb60000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedb80000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedba0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedbc0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedbe0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedc00000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedc20000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedc40000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedc60000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedc80000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedca0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedcc0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedce0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedd00000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedd20000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedd40000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedd60000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedd80000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedda0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffceddc0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedde0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcede00000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcede20000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcede40000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcede60000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcede80000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedea0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedec0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedee0000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedf00000000, 0xffffcc0000000000),
        ::testing::make_tuple(0xffffcedf20000000, 0xffffcc0000000000)));


INSTANTIATE_TEST_CASE_P(
    TestWithParameters_BF_005, MyTest,
    testing::Values(
        // start: 97495757619
        // stop:  97548186419
        // inc:   1048576
        ::testing::make_tuple(0xbe66666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe68666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe6a666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe6c666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe6e666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe70666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe72666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe74666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe76666660000000, 0xbe70000000000000),
        ::testing::make_tuple(0xbe78666660000000, 0xbe80000000000000),
        ::testing::make_tuple(0xbe7a666660000000, 0xbe80000000000000),
        ::testing::make_tuple(0xbe7c666660000000, 0xbe80000000000000),
        ::testing::make_tuple(0xbe7e666660000000, 0xbe80000000000000),
        ::testing::make_tuple(0xbe80666660000000, 0xbe80000000000000),
        ::testing::make_tuple(0xbe82666660000000, 0xbe80000000000000),
        ::testing::make_tuple(0xbe84666660000000, 0xbe88000000000000),
        ::testing::make_tuple(0xbe86666660000000, 0xbe88000000000000),
        ::testing::make_tuple(0xbe88666660000000, 0xbe88000000000000),
        ::testing::make_tuple(0xbe8a666660000000, 0xbe88000000000000),
        ::testing::make_tuple(0xbe8c666660000000, 0xbe90000000000000),
        ::testing::make_tuple(0xbe8e666660000000, 0xbe90000000000000),
        ::testing::make_tuple(0xbe90666660000000, 0xbe90000000000000),
        ::testing::make_tuple(0xbe92666660000000, 0xbe94000000000000),
        ::testing::make_tuple(0xbe94666660000000, 0xbe94000000000000),
        ::testing::make_tuple(0xbe96666660000000, 0xbe98000000000000),
        ::testing::make_tuple(0xbe98666660000000, 0xbe98000000000000),
        ::testing::make_tuple(0xbe9a666660000000, 0xbe9c000000000000),
        ::testing::make_tuple(0xbe9c666660000000, 0xbe9c000000000000),
        ::testing::make_tuple(0xbe9e666660000000, 0xbea0000000000000),
        ::testing::make_tuple(0xbea0666660000000, 0xbea0000000000000),
        ::testing::make_tuple(0xbea2666660000000, 0xbea2000000000000),
        ::testing::make_tuple(0xbea4666660000000, 0xbea4000000000000),
        ::testing::make_tuple(0xbea6666660000000, 0xbea6000000000000),
        ::testing::make_tuple(0xbea8666660000000, 0xbea8000000000000),
        ::testing::make_tuple(0xbeaa666660000000, 0xbeaa000000000000),
        ::testing::make_tuple(0xbeac666660000000, 0xbeac000000000000),
        ::testing::make_tuple(0xbeae666660000000, 0xbeae000000000000),
        ::testing::make_tuple(0xbeb0666660000000, 0xbeb0000000000000),
        ::testing::make_tuple(0xbeb2666660000000, 0xbeb2000000000000),
        ::testing::make_tuple(0xbeb4666660000000, 0xbeb4000000000000),
        ::testing::make_tuple(0xbeb6666660000000, 0xbeb6000000000000),
        ::testing::make_tuple(0xbeb8666660000000, 0xbeb8000000000000),
        ::testing::make_tuple(0xbeba666660000000, 0xbeba000000000000),
        ::testing::make_tuple(0xbebc666660000000, 0xbebc000000000000),
        ::testing::make_tuple(0xbebe666660000000, 0xbebe000000000000),
        ::testing::make_tuple(0xbec0666660000000, 0xbec0800000000000),
        ::testing::make_tuple(0xbec2666660000000, 0xbec2800000000000),
        ::testing::make_tuple(0xbec4666660000000, 0xbec4800000000000),
        ::testing::make_tuple(0xbec6666660000000, 0xbec6800000000000),
        ::testing::make_tuple(0xbec8666660000000, 0xbec8800000000000)));
