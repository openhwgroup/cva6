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
 *  Description: Generic RAM model
 */
#ifndef __RAM_MODEL_H__
#define __RAM_MODEL_H__

#include <array>
#include <memory>
#include <cstdint>
#include <cstring>

template <size_t N>
class ram_model
{
public:

    ram_model(const char* name) : name_m(name)
    {
        mem_m  = std::make_shared<std::array<uint8_t, N>>();
        bmap_m = std::make_shared<std::array<uint8_t, N/8>>();

        memset(bmap_m->data(), 0, N/8);
    }

    ~ram_model()
    {
    }

    uint8_t* getMemPtr()
    {
        return mem_m->data();
    }

    const char* getName()
    {
        return name_m.c_str();
    }

    void read(uint8_t *buf, size_t n, uint64_t addr, uint8_t *valid = nullptr)
    {
        uint64_t off = addr % N;

        if (valid != nullptr) {
            memset(valid, 0, (n + 7)/8);
        }

        for (size_t i = 0; i < n; ++i) {
            uint8_t rdata;
            rdata = (*mem_m)[off + i];
            if (valid != nullptr) {
                if (getBmap(off + i)) {
                    setBit(valid[i/8], i % 8);
                }
            }
            buf[i] = rdata;

#if DEBUG
            std::cout << "reading @0x"
                << std::hex
                << off + i
                << " / rdata = 0x"
                << (unsigned)rdata
                << std::dec << std::endl;
#endif
        }
    }

    void write(const uint8_t *buf, const uint8_t *be, size_t n, uint64_t addr)
    {
        uint64_t off = addr % N;
        for (size_t i = 0; i < n; ++i) {
            if (getBit(be[i / 8], i % 8)) {
                (*mem_m)[off + i] = buf[i];
                setBmap(off + i);

#if DEBUG
                std::cout << "writing @0x"
                    << std::hex
                    << off + i
                    << " / wdata = 0x"
                    << (unsigned)buf[i]
                    << std::dec << std::endl;
#endif
            }
        }
    }

    inline bool getBmap(uint64_t addr) const
    {
        uint64_t off = addr % N;
        return getBit((*bmap_m)[off / 8], off % 8) ? true : false;
    }

protected:

    static inline int getBit(uint8_t byte, size_t pos)
    {
        return (byte >> pos) & 0x1;
    }

    static inline void setBit(uint8_t &byte, size_t pos)
    {
        byte |= (1 << pos);
    }

    inline void setBmap(uint64_t addr)
    {
        uint64_t off = addr % N;
         setBit((*bmap_m)[off / 8], off % 8);
    }

    std::string name_m;
    std::shared_ptr<std::array<uint8_t, N  >> mem_m;
    std::shared_ptr<std::array<uint8_t, N/8>> bmap_m;
};

#endif /* __ram_model_H__ */
