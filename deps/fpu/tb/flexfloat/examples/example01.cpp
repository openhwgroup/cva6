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

#include "flexfloat.hpp"
#include <cstdio>
#include <iostream>

int main(){

	double dbl;

        // Double-precision variables
        flexfloat<11, 52> ff_a, ff_b, ff_c;
        // Assigment with cast (from double literal)
        ff_a = 10.4;
        ff_b = 11.5;
        // Overloaded operators
        ff_b += 2;
        ff_c = ff_a + ff_b;
        // C++ output stream
        std::cout << "[cout] ff_c = " << ff_c << " (" << flexfloat_as_bits << ff_c << ")" << std::endl;
        // C-style printf (it requires an explicit cast)
        printf("[printf] ff_c = %f\n", (double) ff_c);
        // checksum with double result
        if(ff_c == (10.4+11.5+2)) printf("checksum ok\n");
        else printf("checksum WRONG!!!");

        // IEEE float16: 5 bits (exponent) + 11 bits (expliit mantissa)
        flexfloat<5, 10> n1 = 1.11, n2 = 3.754, n3;
        std::cout << "n1+n2 = " << flexfloat_as_double << (n1 + n2) << std::endl;
        // Automatic cast from different precisions
        n3 = ff_c;
        std::cout << "n3 = " << flexfloat_as_double << n3 << flexfloat_as_bits << " (" << n3 << ")" << std::endl;
        // float16 with extended dynamic: : 8 bits (exponent) + 7 bits (explicit mantissa)
        flexfloat<8, 7> n4 = n3;
        std::cout << "n4 = " << flexfloat_as_double << n4 << flexfloat_as_bits << " (" << n4 << ")" << std::endl;
        
	return 0;
}
