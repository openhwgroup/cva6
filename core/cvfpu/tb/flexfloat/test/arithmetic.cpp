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


TEST(floatffArithmeticTest, ResultHasCorrectType)
{
    using doubleff = flexfloat<11, 52>;
    using floatff = flexfloat<8, 23>;

    ::testing::StaticAssertTypeEq<doubleff, decltype(doubleff() + doubleff())>();
    ::testing::StaticAssertTypeEq<doubleff, decltype(doubleff() - doubleff())>();
    ::testing::StaticAssertTypeEq<doubleff, decltype(doubleff() * doubleff())>();
    ::testing::StaticAssertTypeEq<doubleff, decltype(doubleff() / doubleff())>();

    ::testing::StaticAssertTypeEq<floatff, decltype(floatff() + floatff())>();
    ::testing::StaticAssertTypeEq<floatff, decltype(floatff() - floatff())>();
    ::testing::StaticAssertTypeEq<floatff, decltype(floatff() * floatff())>();
    ::testing::StaticAssertTypeEq<floatff, decltype(floatff() / floatff())>();

    doubleff dlhs;
    ::testing::StaticAssertTypeEq<doubleff&, decltype(dlhs += doubleff())>();
    ::testing::StaticAssertTypeEq<doubleff&, decltype(dlhs -= doubleff())>();
    ::testing::StaticAssertTypeEq<doubleff&, decltype(dlhs *= doubleff())>();
    ::testing::StaticAssertTypeEq<doubleff&, decltype(dlhs /= doubleff())>();
    floatff flhs;
    ::testing::StaticAssertTypeEq<floatff&, decltype(flhs += floatff())>();
    ::testing::StaticAssertTypeEq<floatff&, decltype(flhs -= floatff())>();
    ::testing::StaticAssertTypeEq<floatff&, decltype(flhs *= floatff())>();
    ::testing::StaticAssertTypeEq<floatff&, decltype(flhs /= floatff())>();
}


}  // namespace
