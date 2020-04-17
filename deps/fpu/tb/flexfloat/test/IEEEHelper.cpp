/*
   Copyright 2018 - The OPRECOMP Project Consortium, Universitat Jaume I,
                    IBM Research GmbH. All rights reserved.
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

#include "IEEEHelper.h"


#include <bitset>
#include <cassert>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <iostream>


void IEEEHelper::showConfig()
{
    printf("Configuration of format<%u,%u>:\n", _e, _m);
    printf(" p = %u\n", _m + 1);
    printf(" emax = %i\n", getEmax());
    printf(" emin = %i\n", getEmin());
    printf(" bias = %i\n", getBias());
    printf("Limits:\n");
    printf(" max: %5e \t = %.20f\n", maxValue(), maxValue());
    printf(" sNr: %5e \t = %.20f\n", smallestNormalValue(),
           smallestNormalValue());
    printf(" lSN: %5e \t = %.20f\n", maxSubnormalValue(), maxSubnormalValue());
    printf(" sSN: %5e \t = %.20f\n", minSubnormalValue(), minSubnormalValue());
    printf("Cases (one-sided):\n");
    printf(" Normal: %i \t = %u*%u\n", countNormalRange(), countExpRange(),
           countSubnormalRange());
    printf(" Subnormal: %i\n", countSubnormalRange());
    printf(" NAN/INFs: %i\n", countSubnormalRange());
    printf(" 2^(E+M) = %i = (sum over #cases one side) = %u\n",
           (int)pow(2, _e + _m),
           countNormalRange() + 2 * countSubnormalRange());
    printf("\n");
}

double IEEEHelper::iterateNormalRange(int ie, int im)
{
    assert(ie >= 0);
    assert(ie < _NnormalExp);
    assert(im >= 0);
    assert(im < _Nsubnormal);

    double m = 1.0 + im * pow(2.0, -_m);
    // printf("im = %i, m = %f\n", im, m );
    return pow(2.0, ie + getEmin()) * m;
}

double IEEEHelper::iterateSubnormalRange(int im)
{
    assert(im >= 0);
    assert(im < _Nsubnormal);

    double m = 0.0 + im * pow(2.0, -_m);
    return pow(2.0, getEmin()) * m;
}

void show(uint64_t u)
{
    printf("%016lx\t", u);
    std::cout << std::bitset<64>(u) << std::endl;
}

#define CAST_DOUBLE_TO_UINT64(d) (*((uint64_t*)(&(d))))
#define CAST_UINT64_TO_DOUBLE(d) (*((double*)(&(d))))

void show(double d)
{
    printf("%.20e\t", d);
    uint64_t u = CAST_DOUBLE_TO_UINT64(d);
    printf("0x%016lx\t", u);
    std::cout << std::bitset<64>(u) << std::endl;
}

void showTable(IEEEHelper& h)
{
    int ne = h.countExpRange();
    int nm = h.countSubnormalRange();

    printf("Subnormal Range:\n");

    for (int im = 0; im < nm; ++im) {
        double d = h.iterateSubnormalRange(im);
        printf("%5i/%5i: \t %.20e \t %f \n", im, nm, d, d);
    }

    printf("Normal Range:\n");
    for (int ie = 0; ie < ne; ++ie) {
        for (int im = 0; im < nm; ++im) {
            double d = h.iterateNormalRange(ie, im);
            printf("(%5i,%5i)/(%5i,%5i): \t %.20e \t %f \n", ie, im, ne, nm, d,
                   d);
        }
    }
}


// int main(int argc, char **argv)
// {
//     if( argc != 2+1 )
//     {
//         printf("Usage: %s <E> <M>\n", argv[0]);
//         exit(1);
//     }

//     int e = atoi( argv[1]);
//     int m = atoi( argv[2]);

// 	IEEEHelper h = IEEEHelper(e,m);

// 	h.showConfig();
// 	show( h );

// 	return 0;
// }
