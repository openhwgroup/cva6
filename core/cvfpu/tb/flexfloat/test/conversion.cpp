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

#include <bitset>

#include <gtest/gtest.h>
#include <flexfloat.hpp>


namespace {

TEST(FlexFloatConversionTest, PreservesPrecision) {
    #ifdef FLEXFLOAT_ON_SINGLE
    const fp_t val = 1.0f + 1e-5f;
    #endif
    #ifdef FLEXFLOAT_ON_DOUBLE
    const fp_t val = 1.0 + 1e-14;
    #endif
    #ifdef FLEXFLOAT_ON_QUAD
    const fp_t val = 1.0q + 1e-56q;
    #endif
    EXPECT_EQ(val, fp_t(flexfloat<NUM_BITS_EXP, NUM_BITS_FRAC>(val)));
}

#ifdef FLEXFLOAT_ON_DOUBLE
TEST(FlexFloatConversionTest, LowersPrecision) {
    const double val = 1.0 + 1e-15;
    EXPECT_NE(val, double(flexfloat<8, 23>(val)));  // round to float
}
#endif

TEST(FlexFloatConversionTest, HandlesDenormals) {
    EXPECT_EQ(0.25, fp_t(flexfloat<2, 3>(0.25)));
    EXPECT_EQ(0.75, fp_t(flexfloat<2, 3>(0.75)));
}

TEST(FlexFloatConversionTest, ConvertsBetweenFlexFloat) {
    const double val = 1.0 + 1e-14;
    flexfloat<11, 52> d_val(val);
    flexfloat<8, 23> s_val(d_val);
    EXPECT_NE(val, double(s_val));
    EXPECT_EQ(float(val), float(s_val));
}

TEST(FlexFloatConversionTest, ConvertsToBits) {
    #ifdef FLEXFLOAT_ON_SINGLE
    const fp_t val = 1.0f + 1e-5f;
    #endif
    #ifdef FLEXFLOAT_ON_DOUBLE
    const fp_t val = 1.0 + 1e-14;
    #endif
    #ifdef FLEXFLOAT_ON_QUAD
    const fp_t val = 1.0q + 1e-56q;
    #endif
    ::testing::StaticAssertTypeEq<
        std::bitset<sizeof(val)*8>,
        decltype(bits(flexfloat<11, 52>(val)))>();
    ::testing::StaticAssertTypeEq<
        std::bitset<sizeof(val)*8>,
        decltype(bits(flexfloat<8, 23>(val)))>();
    #ifdef FLEXFLOAT_ON_SINGLE
    EXPECT_NE(bits(val), bits(flexfloat<11, 52>(val)));
    EXPECT_EQ(bits(val), bits(flexfloat<8, 23>(val)));
    #endif
    #ifdef FLEXFLOAT_ON_DOUBLE
    EXPECT_EQ(bits(val), bits(flexfloat<11, 52>(val)));
    EXPECT_NE(bits(val), bits(flexfloat<8, 23>(val)));
    #endif
}

TEST(FlexFloatConversionTest, ConvertsToString) {
    flexfloat<4, 5> val1 = 1.0;
    EXPECT_EQ("0-0111-00000", bitstring(val1));
    flexfloat<3, 2> val2 = 1.75;
    EXPECT_EQ("0-011-11", bitstring(val2));
    flexfloat<5, 7> val3 = 0.0;
    EXPECT_EQ("0-00000-0000000", bitstring(val3));
}

} // namespace
