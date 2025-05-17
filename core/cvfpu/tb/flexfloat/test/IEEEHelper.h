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

#pragma once

#include <cmath>

// ### IEEE 754 HELPER FUNCTIONS

class IEEEHelper {
private:
    int _e;
    int _m;
    int _emax;
    int _emin;

    long long int _Nnormal;
    long long int _NnormalExp;
    long long int _Nsubnormal;

public:
    IEEEHelper(int e, int m)
    {
        _e = e;
        _m = m;

        _Nnormal = (getEmax() - getEmin() + 1) * pow(2.0, _m);
        _NnormalExp = (getEmax() - getEmin() + 1);
        _Nsubnormal = pow(2.0, _m);
    }

    inline int getEmax() { return pow(2.0, _e - 1) - 1; }
    inline int getEmin() { return 1 - getEmax(); }
    inline int getBias() { return getEmax(); }

    inline double getMmin() { return pow(2.0, -_m); }            // use p = m+1
    inline double getMmaxNormal() { return 2 - pow(2.0, -_m); }  // use p = m+1
    inline double getMmaxSubnormal()
    {
        return 1 - pow(2.0, -_m);
    }  // use p = m+1

    inline double maxValue() { return pow(2.0, getEmax()) * getMmaxNormal(); }
    inline double smallestNormalValue() { return pow(2.0, getEmin()); }
    inline double maxSubnormalValue()
    {
        return pow(2.0, getEmin()) * getMmaxSubnormal();
    }
    inline double minSubnormalValue()
    {
        return pow(2.0, getEmin()) * getMmin();
    }

    void showConfig();

    int countNormalRange() { return _Nnormal; }
    int countExpRange() { return _NnormalExp; }
    int countSubnormalRange() { return _Nsubnormal; }

    double iterateNormalRange(int ie, int im);
    double iterateSubnormalRange(int i);
};

void show(double d);
void showTable(IEEEHelper& h);
