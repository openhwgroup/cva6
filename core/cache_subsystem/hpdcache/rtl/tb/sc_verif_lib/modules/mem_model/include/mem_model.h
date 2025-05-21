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
 *  Description: Generic Memory model
 */
#ifndef __MEM_MODEL_H__
#define __MEM_MODEL_H__

#include <map>
#include <cstdint>

class mem_model
{
public:

    enum mem_model_init_mode_e
    {
        MEM_MODEL_INIT_VALUE,
        MEM_MODEL_INIT_RANDOM
    };

    typedef std::map<uint64_t, uint64_t>  mem_array_t;
    typedef std::pair<uint64_t, uint64_t> mem_array_pair_t;

    mem_model(const char* name,
              mem_model_init_mode_e init_mode = MEM_MODEL_INIT_RANDOM,
              uint64_t              init_val  = 0) :
            name_m(name),
            init_mode_m(MEM_MODEL_INIT_RANDOM),
            init_val_m(init_val)
    {
    }

    ~mem_model()
    {
    }

    mem_array_t *getMemPtr()
    {
        return &mem_array_m;
    }

    const char* getName()
    {
        return name_m.c_str();
    }

    uint64_t readMemory(uint64_t word_addr)
    {
        mem_array_t::const_iterator it;

        //  check if the target address was already accessed
        it = mem_array_m.find(word_addr);
        if (it != mem_array_m.end()) {
            return it->second;
        }

        //  addr not found, thus add it to the memory and return the init number
        uint64_t value;
        switch (init_mode_m) {
            case MEM_MODEL_INIT_RANDOM:
                value = ((uint64_t)rand() << 32) | (uint64_t)rand();
                break;
            case MEM_MODEL_INIT_VALUE:
                value = init_val_m;
                break;
        }
        mem_array_m.insert(mem_array_pair_t(word_addr, value));
        return value;
    }

    void writeMemory(uint64_t word_addr, uint64_t data, uint64_t mask)
    {
        mem_array_t::iterator it;

        //  check if the target address was already accessed
        it = mem_array_m.find(word_addr);
        if (it != mem_array_m.end()) {
            it->second = (it->second & ~mask) | (data & mask);
            return;
        }

        //  address not found, thus add it to the memory and merge the
        //  written data with random data
        uint64_t value;
        switch (init_mode_m) {
            case MEM_MODEL_INIT_RANDOM:
                value = ((uint64_t)rand() << 32) | (uint64_t)rand();
                break;
            case MEM_MODEL_INIT_VALUE:
                value = init_val_m;
                break;
        }
        uint64_t newval = (value & ~mask) | (data & mask);
        mem_array_m.insert(mem_array_pair_t(word_addr, newval));
    }

    static uint64_t beToMask(uint8_t be)
    {
        uint64_t mask;

        //  compute the write mask
        mask = 0;
        for (int j = 0; j < 8; j++) {
            if ((be >> j) & 1) {
                mask |= (0xffull) << (j*8);
            }
        }

        return mask;
    }

protected:

    std::string name_m;
    mem_array_t mem_array_m;
    mem_model_init_mode_e init_mode_m;
    uint64_t init_val_m;
};

#endif /* __MEM_MODEL_H__ */
