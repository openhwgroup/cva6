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

#include "flexfloat.h"
#include <stdio.h>

int main(){

    double dbl;

    #ifdef FLEXFLOAT_STATS
    ff_start_stats();
    #else
    printf("WARNING: Collection of statistics is not enabled by default, execute \"cd <build_dir> && cmake -DENABLE_STATS=ON <src_dir> && make\"\n");
    #endif
    // Double-precision variables
    flexfloat_t ff_a, ff_b, ff_c;
    ff_init_double(&ff_a, 10.4, (flexfloat_desc_t) {11, 52});
    ff_init_double(&ff_b, 11.5, (flexfloat_desc_t) {11, 52});
    ff_init(&ff_c, (flexfloat_desc_t) {11, 52});

    // Arithmetic operators
    ff_add(&ff_c, &ff_a, &ff_b); // c=a+b
    ff_add(&ff_c, &ff_c, &ff_b); // c=c+b
    ff_sub(&ff_c, &ff_c, &ff_b); // c=c-b
    ff_mul(&ff_c, &ff_c, &ff_a); // c=c*b

    // IEEE float16: 5 bits (exponent) + 10 bits (explicit mantissa)
    flexfloat_t n1, n2, n3, n4;
    ff_init_double(&n1, 1.11, (flexfloat_desc_t) {5, 10});
    ff_init_double(&n2, 3.754, (flexfloat_desc_t) {5, 10});
    ff_init(&n3, (flexfloat_desc_t) {5, 10});
    ff_add(&n3, &n1, &n2);
    ff_div(&n3, &n1, &n2);

    // Casts
    ff_cast(&n3, &ff_c, (flexfloat_desc_t) {5, 10}); //  n3 = ff_c;
    ff_cast(&n4, &n3, (flexfloat_desc_t) {8, 7}); // n4 = n3

    #ifdef FLEXFLOAT_STATS
    ff_print_stats();
    #endif

    return 0;
}