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
 *  Description: Class definition of a cache directory using a Pseudo-LRU
 *               replacement policy
 */
#ifndef __GENERIC_CACHE_DIRECTORY_PLRU_H__
#define __GENERIC_CACHE_DIRECTORY_PLRU_H__

#include <systemc>
#include <string>

#include "generic_cache_directory_base.h"

class GenericCacheDirectoryPlru : public GenericCacheDirectoryBase
{
    bool      *plru_m;

public:

    GenericCacheDirectoryPlru(const std::string &name,
                              size_t            nways,
                              size_t            nsets,
                              size_t            nbytes)
            : GenericCacheDirectoryBase(name, nways, nsets, nbytes)
    {
        plru_m = new bool [nways*nsets];
    }

    ~GenericCacheDirectoryPlru()
    {
        delete [] plru_m;
    }

    bool &getCachePlru(size_t way, size_t set)
    {
        return plru_m[way*sets_m + set];
    }

    void reset()
    {
        GenericCacheDirectoryBase::reset();

        for (size_t way = 0; way < ways_m; way++) {
            for (size_t set = 0; set < sets_m; set++) {
                getCachePlru(way, set) = false;
            }
        }
    }

    virtual bool repl(uint64_t  addr,
                      uint64_t* victim_tag,
                      size_t*   victim_way,
                      size_t*   victim_set)
    {
        uint64_t tag;
        size_t set;

        set = getAddrSet(addr);
        tag = getAddrTag(addr);

        //  look if there is an empty way
        for (size_t way = 0; way < ways_m; way++) {
            if (!getCacheValid(way, set)) {
                if (victim_tag != nullptr) {
                    *victim_tag = 0;
                }
                if (victim_way != nullptr) {
                    *victim_way = way;
                }
                if (victim_set != nullptr) {
                    *victim_set = set;
                }
                //  set the new information
                getCacheValid(way, set) = true;
                getCacheTag(way, set)   = tag;
                replUpdate(way, set);
                return false;
            }
        }

        //  look for a non-recently used way (plru bit unset)
        for (size_t way = 0; way < ways_m; way++) {
            if (!getCachePlru(way, set)) {
                //  get victim entry informations
                if (victim_tag != nullptr) {
                    *victim_tag = getCacheTag(way, set);
                }
                if (victim_way != nullptr) {
                    *victim_way = way;
                }
                if (victim_set != nullptr) {
                    *victim_set = set;
                }

                //  set the new information
                getCacheTag(way, set) = tag;
                replUpdate(way, set);
                return true;
            }
        }

        sc_assert(false && "error: all plru bits are set");
        return false;
    }

    virtual void replUpdate(size_t way, size_t set)
    {
        bool reset;

        //  set the accessed way to recently used
        getCachePlru(way, set) = true;

        //  check if all recently used bits are set
        reset = true;
        for (int _way = 0; _way < ways_m; _way++) {
            reset = reset && getCachePlru(_way, set);
        }

        //  if all PLRU bits are set, reset them all but the last accessed one
        if (reset) {
            for (int _way = 0; _way < ways_m; _way++) {
                if (_way != way) {
                    getCachePlru(_way, set) = false;
                }
            }
        }
    }
};

#endif /* __GENERIC_CACHE_DIRECTORY_PLRU_H__ */
