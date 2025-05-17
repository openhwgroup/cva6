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
 *  Description: Class definition of a generic cache data
 */
#ifndef __GENERIC_CACHE_DATA_H__
#define __GENERIC_CACHE_DATA_H__

#include <systemc>
#include <string>

class GenericCacheData
{
public:

    GenericCacheData(const std::string &name,
                     size_t            nways,
                     size_t            nsets,
                     size_t            nwords)
        : name_m(name),
          data_m(nways*nsets*nwords, 0),
          ways_m(nways),
          sets_m(nsets),
          words_m(nwords)
    {
        sc_assert(nsets > 0);
        sc_assert(nways > 0);
        sc_assert(nwords > 0);
    }

    ~GenericCacheData()
    {
    }

    inline uint64_t getAddrSet(uint64_t addr)
    {
        return (addr / (words_m * 8)) % sets_m;
    }

    inline uint64_t getAddrWord(uint64_t addr)
    {
        return (addr / 8) % words_m;
    }

    inline void write(uint64_t wdata, uint8_t be, size_t way, size_t set, size_t word)
    {
        uint64_t mask = 0;
        for (int i = 0; i < 8; i++) {
            if ((be >> i) & 0x1) {
                mask |= 0xff << (i*8);
            }
        }

        uint64_t prev = getCacheData(way, set, word);
        getCacheData(way, set, word) = (prev & ~mask) | (wdata & mask);;

#ifdef DEBUG_GENERIC_CACHE_DATA
        std::cout << "DEBUG: cache data : writing "
                  << "0x" << std::hex << getCacheData(way, set, word) << std::dec
                  << " / set = "
                  << set
                  << " / way = "
                  << way
                  << " / word = "
                  << word
                  << std::endl;
#endif
    }

    inline uint64_t read(size_t way, size_t set, size_t word)
    {
        uint64_t ret = getCacheData(way, set, word);

#ifdef DEBUG_GENERIC_CACHE_DATA
        std::cout << "DEBUG: cache data : reading "
                  << "0x" << std::hex << ret << std::dec
                  << " / set = "
                  << set
                  << " / way = "
                  << way
                  << " / word = "
                  << word
                  << std::endl;
#endif

        return ret;
    }

protected:

    std::string               name_m;
    std::vector<uint64_t>     data_m;

    size_t ways_m;
    size_t sets_m;
    size_t words_m;

    inline uint64_t &getCacheData(size_t way, size_t set, size_t word)
    {
        return data_m[way*(sets_m*words_m) + (set*words_m) + word];
    }
};

#endif
