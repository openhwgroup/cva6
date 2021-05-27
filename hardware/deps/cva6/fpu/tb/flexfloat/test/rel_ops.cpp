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

namespace {

void show(double d)
{
    printf("%.20e\t", d);
    uint64_t u = *((uint64_t *) &d);
    printf("0x%016lx\t", u);
    std::cout << std::bitset<64>(u) << std::endl;
}

TEST(flexfloatRelOpsTest, Equal)
{
    using doubleff = flexfloat<11, 52>;
    using floatff  = flexfloat<8, 23>;
    const double val1 = 1.0 + 1e-15;
    const double val2 = 1.0 + 2e-15;
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_TRUE(doubleff(val1) == doubleff(val1));
    EXPECT_FALSE(doubleff(val1) == doubleff(val2));
    #endif
    EXPECT_TRUE(floatff(val1) == floatff(val1));

    EXPECT_TRUE(floatff(val1) == floatff(val2));    // due to rounding
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_FALSE(doubleff(floatff(val1)) == doubleff(val1));  // due to rounding
    EXPECT_FALSE(doubleff(floatff(val1)) == doubleff(val2));  // due to rounding
    #endif
}


TEST(flexfloatRelOpsTest, NotEqual)
{
    using doubleff = flexfloat<11, 52>;
    using floatff  = flexfloat<8, 23>;
    const double val1 = 1.0 + 1e-15;
    const double val2 = 1.0 + 2e-15;
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_FALSE(doubleff(val1) != doubleff(val1));
    EXPECT_TRUE(doubleff(val1) != doubleff(val2));
    #endif
    EXPECT_FALSE(floatff(val1) != floatff(val1));
    EXPECT_FALSE(floatff(val1) != floatff(val2));  // due to rounding
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_TRUE(doubleff(floatff(val1)) != doubleff(val1));  // due to rounding
    EXPECT_TRUE(doubleff(floatff(val1)) != doubleff(val2));  // due to rounding
    #endif
}


TEST(flexfloatRelOpsTest, LessThan)
{
    using doubleff = flexfloat<11, 52>;
    using floatff  = flexfloat<8, 23>;
    const double val1 = 1.0 + 1e-15;
    const double val2 = 1.0 + 2e-15;
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_FALSE(doubleff(val1) < doubleff(val1));
    EXPECT_FALSE(doubleff(val2) < doubleff(val1));
    EXPECT_TRUE(doubleff(val1) < doubleff(val2));
    #endif
    EXPECT_FALSE(floatff(val1) < floatff(val1));
    EXPECT_FALSE(floatff(val2) < floatff(val1));
    EXPECT_FALSE(floatff(val1) < floatff(val2));  // due to rounding
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_TRUE(doubleff(floatff(val1)) < doubleff(val1));  // due to rounding
    EXPECT_TRUE(doubleff(floatff(val2)) < doubleff(val1));  // due to rounding
    EXPECT_TRUE(doubleff(floatff(val1)) < doubleff(val2));  // due to rounding
    #endif
}


TEST(flexfloatRelOpsTest, LessOrEqual)
{
    using doubleff = flexfloat<11, 52>;
    using floatff  = flexfloat<8, 23>;
    const double val1 = 1.0 + 1e-15;
    const double val2 = 1.0 + 2e-15;
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_TRUE(doubleff(val1) <= doubleff(val1));
    EXPECT_FALSE(doubleff(val2) <= doubleff(val1));
    EXPECT_TRUE(doubleff(val1) <= doubleff(val2));
    #endif
    EXPECT_TRUE(floatff(val1) <= floatff(val1));
    EXPECT_TRUE(floatff(val2) <= floatff(val1));  // due to rounding
    EXPECT_TRUE(floatff(val1) <= floatff(val2));
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_TRUE(doubleff(floatff(val1)) <= doubleff(val1));
    EXPECT_TRUE(doubleff(floatff(val2)) <= doubleff(val1));  // due to rounding
    EXPECT_TRUE(doubleff(floatff(val1)) <= doubleff(val2));
    #endif
}


TEST(flexfloatRelOpsTest, GreaterThan)
{
    using doubleff = flexfloat<11, 52>;
    using floatff = flexfloat<8, 23>;
    const double val1 = 1.0 + 1e-15;
    const double val2 = 1.0 + 2e-15;
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_FALSE(doubleff(val1) > doubleff(val1));
    EXPECT_TRUE(doubleff(val2) > doubleff(val1));
    EXPECT_FALSE(doubleff(val1) > doubleff(val2));
    #endif
    EXPECT_FALSE(floatff(val1) > floatff(val1));
    EXPECT_FALSE(floatff(val2) > floatff(val1));  // due to rounding
    EXPECT_FALSE(floatff(val1) > floatff(val2));
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_FALSE(doubleff(floatff(val1)) > doubleff(val1));
    EXPECT_FALSE(doubleff(floatff(val2)) > doubleff(val1));  // due to rounding
    EXPECT_FALSE(doubleff(floatff(val1)) > doubleff(val2));
    #endif
}


TEST(flexfloatRelOpsTest, GreaterOrEqual)
{
    using doubleff = flexfloat<11, 52>;
    using floatff = flexfloat<8, 23>;
    const double val1 = 1.0 + 1e-15;
    const double val2 = 1.0 + 2e-15;
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_TRUE(doubleff(val1) >= doubleff(val1));
    EXPECT_TRUE(doubleff(val2) >= doubleff(val1));
    EXPECT_FALSE(doubleff(val1) >= doubleff(val2));
    #endif
    EXPECT_TRUE(floatff(val1) >= floatff(val1));
    EXPECT_TRUE(floatff(val2) >= floatff(val1));    // due to rounding
    EXPECT_TRUE(floatff(val1) >= floatff(val2));    // due to rounding
    #ifndef FLEXFLOAT_ON_SINGLE
    EXPECT_FALSE(doubleff(floatff(val1)) >= doubleff(val1));  // due to rounding
    EXPECT_FALSE(doubleff(floatff(val2)) >= doubleff(val1));  // due to rounding
    EXPECT_FALSE(doubleff(floatff(val1)) >= doubleff(val2));
    #endif
}


}  // namespace