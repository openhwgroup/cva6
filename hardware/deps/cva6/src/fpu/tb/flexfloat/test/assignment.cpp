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


TEST(FlexFloatAssignmentTest, PreservesPrecision) {
    #ifdef FLEXFLOAT_ON_SINGLE
    const fp_t val = 1.0f + 1e-5f;
    #endif
    #ifdef FLEXFLOAT_ON_DOUBLE
    const fp_t val = 1.0 + 1e-14;
    #endif
    #ifdef FLEXFLOAT_ON_QUAD
    const fp_t val = 1.0q + 1e-56q;
    #endif
    flexfloat<NUM_BITS_EXP, NUM_BITS_FRAC> ff_val;
    ff_val = val;
    EXPECT_EQ(val, fp_t(ff_val));
}

TEST(FlexFloatAssignmentTest, LowersPrecision) {
    const double val = 1.0 + 1e-15;
    flexfloat<8, 23> ff_val;
    ff_val = val;
    EXPECT_NE(val, double(ff_val));  // round to float
}


TEST(FlexFloatAssignmentTest, AssignsBetweenFormats) {
    const double val = 1.0 + 1e-15;
    flexfloat<11, 52> d_val(val);
    flexfloat<8, 23> s_val;
    s_val = d_val;
    EXPECT_NE(val, double(s_val));
    EXPECT_EQ(float(val), float(s_val));
}


} // namespace

