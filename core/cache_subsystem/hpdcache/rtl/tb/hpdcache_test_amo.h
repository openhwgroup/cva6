/**
 *  Copyright 2023,2024 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/**
 *  Author     : Cesar Fuguet
 *  Date       : October, 2024
 *  Description: Atomic Memory Operations (AMO) Utility Class
 */
#ifndef __HPDCACHE_TEST_AMO_H__
#define __HPDCACHE_TEST_AMO_H__

#include <iostream>

class hpdcache_test_transaction_req;

class hpdcache_test_amo
{
protected:

    hpdcache_test_amo()
    {
        /* empty */
    }

    ~hpdcache_test_amo()
    {
        /* empty */
    }

public:

    static uint64_t compute_amo(
            unsigned atop,
            uint64_t ld_data,
            uint64_t st_data,
            unsigned bytes)
    {
        bool umax = (ld_data > st_data);
        bool smax;
        if (bytes == 4) {
            smax = ((int64_t)((int32_t)ld_data) > (int64_t)((int32_t)st_data));
        } else {
            smax =          (((int64_t)ld_data) >          ((int64_t)st_data));
        }

        uint64_t result;
        switch (atop) {
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_SWAP:
                result = st_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_ADD:
                result = ld_data + st_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_AND:
                result = ld_data & st_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_OR:
                result = ld_data | st_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_XOR:
                result = ld_data ^ st_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MAX:
                result = smax ? ld_data : st_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MAXU:
                result = umax ? ld_data : st_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MIN:
                result = smax ? st_data : ld_data; break;
            case hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MINU:
                result = umax ? st_data : ld_data; break;
            default:
                sc_assert(false && "unknown atomic operation"); return 0;
        }

        return result;
    }
};

#endif /* __HPDCACHE_TEST_AMO_H__ */
