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
 *  Description: Class definition of a generic cache directory
 */
#ifndef __GENERIC_CACHE_DIRECTORY_BASE_H__
#define __GENERIC_CACHE_DIRECTORY_BASE_H__

#include <systemc>
#include <string>

class GenericCacheDirectoryBase
{
protected:

    std::string name_m;
    uint64_t    *tag_m;
    bool        *val_m;

    size_t      ways_m;
    size_t      sets_m;
    size_t      bytes_m;

public:

    GenericCacheDirectoryBase(const std::string &name,
                              size_t            nways,
                              size_t            nsets,
                              size_t            nbytes)
        : name_m(name),
          ways_m(nways),
          sets_m(nsets),
          bytes_m(nbytes)
    {
        sc_assert(nsets > 0);
        sc_assert(nways > 0);
        sc_assert(nbytes > 0);

        tag_m = new uint64_t [nways*nsets];
        val_m = new bool     [nways*nsets];
    }

    ~GenericCacheDirectoryBase()
    {
        delete [] tag_m;
        delete [] val_m;
    }

    inline const size_t& getWays() const
    {
        return ways_m;
    }

    inline const size_t& getSets() const
    {
        return sets_m;
    }

    inline const size_t& getBytesPerLine() const
    {
        return bytes_m;
    }

    inline uint64_t &getCacheTag(size_t way, size_t set)
    {
        return tag_m[(way*sets_m) + set];
    }

    inline bool &getCacheValid(size_t way, size_t set)
    {
        return val_m[(way*sets_m) + set];
    }

    inline uint64_t getNline(uint64_t tag, size_t set)
    {
        return tag*sets_m + set;
    }

    inline uint64_t getNline(uint64_t addr)
    {
        return addr / bytes_m;
    }

    inline uint64_t getAddr(uint64_t tag, size_t set)
    {
        return getNline(tag, set) * bytes_m;
    }

    inline uint64_t getAddrTag(uint64_t addr)
    {
        return addr / (sets_m * bytes_m);
    }

    inline uint64_t getAddrSet(uint64_t addr)
    {
        return (addr / bytes_m) % sets_m;
    }

    void reset()
    {
        for (unsigned int way = 0; way < ways_m; way++) {
            for (unsigned int set = 0; set < sets_m; set++) {
                getCacheValid(way, set) = false;
                getCacheTag(way, set)   = 0;
            }
        }
    }

    bool hit(uint64_t addr, size_t *hit_way, size_t *hit_set)
    {
        uint64_t tag;
        size_t set;

        set = getAddrSet(addr);
        tag = getAddrTag(addr);
        for (size_t way = 0; way < ways_m; way++)
        {
            if (getCacheValid(way, set) && (tag == getCacheTag(way, set)))
            {
                if (hit_way != nullptr) {
                    *hit_way = way;
                }
                if (hit_set != nullptr) {
                    *hit_set = set;
                }
                return true;
            }
        }
        if (hit_way != nullptr) {
            *hit_way = UINT_MAX;
        }
        if (hit_set != nullptr) {
            *hit_set = UINT_MAX;
        }
        return false;
    }

    inline bool inval(size_t way, size_t set)
    {
        bool ret = getCacheValid(way, set);
        getCacheValid(way,set) = false;
        return ret;
    }

    inline bool inval(uint64_t addr)
    {
        uint64_t tag;
        size_t set;

        set = getAddrSet(addr);
        tag = getAddrTag(addr);

        for (size_t way = 0; way < ways_m; way++) {
            if (getCacheTag(way,set) == tag) {
                getCacheValid(way,set) = false;
                return true;
            }
        }
        return false;
    }

    virtual bool repl(uint64_t addr,
                      uint64_t *victim_tag,
                      size_t   *victim_way,
                      size_t   *victim_set) = 0;

    virtual void replUpdate(size_t way,
                            size_t set) = 0;

    inline bool alloc(uint64_t addr,
               size_t   *alloc_way,
               size_t   *alloc_set,
               uint64_t *victim_tag)
    {
        return repl(addr, victim_tag, alloc_way, alloc_set);
    }

    bool access(uint64_t addr,
                size_t *hit_way,
                size_t *hit_set,
                bool update_repl_flags = true)
    {
        size_t _hit_way;
        size_t _hit_set;

        if (hit(addr, &_hit_way, &_hit_set)) {
            if (update_repl_flags) {
                replUpdate(_hit_way, _hit_set);
            }
            if (hit_way != nullptr) *hit_way = _hit_way;
            if (hit_set != nullptr) *hit_set = _hit_set;
            return true;
        }

        if (hit_way != nullptr) *hit_way = UINT_MAX;
        if (hit_set != nullptr) *hit_set = UINT_MAX;
        return false;
    }

    void printTrace()
    {
        std::cout << name_m << std::endl;

        for (size_t way = 0; way < ways_m ; way++)
        {
            for (size_t set = 0; set < sets_m; set++)
            {
                if (getCacheValid(way, set)) {
                    std::cout << "  set = " << set
                        << " / way = " << way
                        << " / tag = " << std::hex << getCacheTag(way, set) << std::dec
                        << std::endl;
                }
            }
        }
    }

};

#endif
