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

#include "IEEEHelper.h"

// TEST(IEEE_helper, demonstrate ) {
// 	uint16_t e = 3;
// 	uint16_t m = 5;
// 	IEEEHelper h = IEEEHelper(e,m);
// 	h.showConfig();
// 	EXPECT_EQ(1, 1);
// }

class CheckValidRepresentationOfFlexfloat5_10
    : public ::testing::TestWithParam<std::tuple<uint16_t, uint16_t>> {
};

class CheckValidRepresentationOfFlexfloat4_8
    : public ::testing::TestWithParam<std::tuple<uint16_t, uint16_t>> {
};

template <typename T>
void test(double d)
{
    // Test value d.
    T fx = d;
    double recoverd = (double)(fx);

    // the recoverd and the original value are required to be the same.
    ASSERT_EQ(recoverd, d);
}

TEST_P(CheckValidRepresentationOfFlexfloat5_10, subnormal)
{
    uint16_t const e = std::get<0>(GetParam());
    uint16_t const m = std::get<1>(GetParam());

    IEEEHelper h = IEEEHelper(e, m);
    // h.showConfig();
    // printf("Subnormal Range:\n");

    int nm = h.countSubnormalRange();
    for (int im = 0; im < nm; ++im) {
        double d = h.iterateSubnormalRange(im);
        test<flexfloat<5, 10>>(d);
    }
}


TEST_P(CheckValidRepresentationOfFlexfloat5_10, regular)
{
    uint16_t const e = std::get<0>(GetParam());
    uint16_t const m = std::get<1>(GetParam());

    IEEEHelper h = IEEEHelper(e, m);
    // h.showConfig();
    // printf("Normal Range:\n");

    int ne = h.countExpRange();
    int nm = h.countSubnormalRange();

    for (int ie = 0; ie < ne; ++ie) {
        for (int im = 0; im < nm; ++im) {
            double d = h.iterateNormalRange(ie, im);
            test<flexfloat<5, 10>>(d);
        }
    }
}

TEST_P(CheckValidRepresentationOfFlexfloat4_8, subnormal)
{
    uint16_t const e = std::get<0>(GetParam());
    uint16_t const m = std::get<1>(GetParam());

    IEEEHelper h = IEEEHelper(e, m);
    // h.showConfig();
    // printf("Subnormal Range:\n");

    int nm = h.countSubnormalRange();
    for (int im = 0; im < nm; ++im) {
        double d = h.iterateSubnormalRange(im);
        test<flexfloat<4, 8>>(d);
    }
}

TEST_P(CheckValidRepresentationOfFlexfloat4_8, regular)
{
    uint16_t const e = std::get<0>(GetParam());
    uint16_t const m = std::get<1>(GetParam());

    IEEEHelper h = IEEEHelper(e, m);
    // h.showConfig();
    // printf("Normal Range:\n");

    int ne = h.countExpRange();
    int nm = h.countSubnormalRange();

    for (int ie = 0; ie < ne; ++ie) {
        for (int im = 0; im < nm; ++im) {
            double d = h.iterateNormalRange(ie, im);
            test<flexfloat<4, 8>>(d);
        }
    }
}

// SUBSET TEST ON Flexfloat TYPE HALF <5,10>
INSTANTIATE_TEST_CASE_P(TestParams_full_subnormal_range,
                        CheckValidRepresentationOfFlexfloat5_10,
                        testing::Values(::testing::make_tuple(5, 10)));

INSTANTIATE_TEST_CASE_P(
    TestParams_subset_subnormal_range, CheckValidRepresentationOfFlexfloat5_10,
    testing::Values(::testing::make_tuple(2, 3), ::testing::make_tuple(3, 4),
                    ::testing::make_tuple(4, 2), ::testing::make_tuple(4, 8),
                    ::testing::make_tuple(5, 8), ::testing::make_tuple(2, 10)));

// SUBSET TEST ON Flexfloat TYPE HALF <4,8>
INSTANTIATE_TEST_CASE_P(TestParams_full_subnormal_range,
                        CheckValidRepresentationOfFlexfloat4_8,
                        testing::Values(::testing::make_tuple(4, 8)));

INSTANTIATE_TEST_CASE_P(TestParams_subset_subnormal_range,
                        CheckValidRepresentationOfFlexfloat4_8,
                        testing::Values(::testing::make_tuple(2, 3),
                                        ::testing::make_tuple(3, 8),
                                        ::testing::make_tuple(4, 3)));
