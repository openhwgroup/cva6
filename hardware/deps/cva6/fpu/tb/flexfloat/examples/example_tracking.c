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

#ifdef FLEXFLOAT_TRACKING
void cb_func(flexfloat_t *v, void *arg) {
    int index = *(int *)arg;
    printf("[%d] val = %f, error = %f \n ", index, ff_track_get_exact(v), ff_track_get_error(v));
}
#endif

int main(){
    int i;
    flexfloat_t ff_sum, ff_val;

    ff_init_double(&ff_sum, 0.0, (flexfloat_desc_t) {7, 7});
    #ifdef FLEXFLOAT_TRACKING
    ff_track_callback(&ff_sum, cb_func, &i);
    #else
    printf("WARNING: Variable tracking is not enabled by default, execute \"cd <build_dir> && cmake -DENABLE_TRACKING=ON <src_dir> && make\"\n");
    #endif

    for(i=1; i<100; i++) {
        ff_init_double(&ff_val, 1.0/i, (flexfloat_desc_t) {7, 7});
        ff_acc(&ff_sum, &ff_val);
    }

    printf("ff_sum = %f\n", ff_get_double(&ff_sum));

    return 0;
}
