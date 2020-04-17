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

#define nan fp_t(0.0 / 0.0)
#define inf fp_t(1.0 / 0.0)

namespace {

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


// System representation of nan's.
TEST(FloatxNanInfTest, system_nans)
{
    fp_t constnan = 0.0 / 0.0;
    printf("constnan: ");
    show((fp_t)constnan);

    fp_t zero = 0;
    fp_t dynamicnan = zero / zero;
    printf("dynamicnan: ");
    show((fp_t)dynamicnan);

    EXPECT_NE(constnan, dynamicnan);  // holds only for NANs
    EXPECT_NE(constnan, nan);         // holds only for NANs
    EXPECT_NE(dynamicnan, nan);       // holds only for NANs

}

// A NAN CASE
TEST(FloatxNanInfTest, cast_nans)
{
    using T1 = flexfloat<2, 3>;
    #ifdef FLEXFLOAT_ON_SINGLE
    using T2 = flexfloat<7, 21>;
    #endif
    #ifdef FLEXFLOAT_ON_DOUBLE
    using T2 = flexfloat<10, 50>;
    #endif
    #ifdef FLEXFLOAT_ON_QUAD
    using T2 = flexfloat<12, 100>;
    #endif
    T1 a = 0.0 / 0.0;
    T2 b = 0.0;
    b = a;

    fp_t constnan =  nan;

    EXPECT_NE(a, a);    // holds only for NANs
    EXPECT_NE(a, nan);  // holds only for NANs
    EXPECT_EQ(*reinterpret_cast<uint_t*>(&a),
              *reinterpret_cast<uint_t*>(&constnan));

    EXPECT_NE(b, b);    // holds only for NANs
    EXPECT_NE(b, nan);  // holds only for NANs
           
}

// A NAN CASE
TEST(FloatxNanInfTest, DIV_2_47_simple)
{
    using T = flexfloat<2, 47>;
    T a = -(
        7.105427e-15 / 2 -
        1e-17);  // a bit smaller than half of the smallest subnormal in <2,47>
    T b = -(7.105427e-15 / 12.0);
    T c = 0;
    c = a / b;
    EXPECT_EQ(fp_t(a), 0.00000000000000000000);
    EXPECT_EQ(fp_t(b), 0.00000000000000000000);
    EXPECT_NE(c, c);    // holds only for NANs
    EXPECT_NE(c, nan);  // holds only for NANs

    fp_t zero = 0;
    fp_t dynamicnan = zero / zero;

    EXPECT_NE(c, dynamicnan);  // holds only for NANs
}


#ifdef FLEXFLOAT_ROUNDING
// A REGULAR CASE (fixing in subnormal does not cause the inf case here)
TEST(FloatxNanInfTest, DIV_3_3_simple)
{
    using T = flexfloat<3, 3>;
    T a = 0.33333333333333331483;
    T b = 0.11111111111111110494;
    T c = 0;
    c = a / b;
    EXPECT_EQ(fp_t(a), 3.43750000000000000000e-01);
    EXPECT_EQ(fp_t(b), 1.25000000000000000000e-01);
    EXPECT_EQ(fp_t(c), 2.7500000000000000000e-00);
}
#endif

#ifdef FLEXFLOAT_ROUNDING
// A INF CASE.
TEST(FloatxNanInfTest, DIV_3_3_simple_inf)
{
    using T = flexfloat<3, 3>;
    T a = 0.33333333333333331483;
    T b =
        (0.03125000000000000000 / 2 -
         1e-7);  // a bit smaller than half of the smallest subnormal in <3,3>
    T c = 0;
    c = a / b;

    // printf("a: 			"); show((fp_t)a);
    // printf("b: 			"); show((fp_t)b);
    // printf("c:   		"); show((fp_t)c);
    // printf("inf: 		"); show((fp_t)inf);

    EXPECT_EQ(fp_t(a), 3.43750000000000000000e-01);
    EXPECT_EQ(fp_t(b), 00000000000000000000);
    EXPECT_EQ(fp_t(c), inf);
}
#endif

}  // namespace
