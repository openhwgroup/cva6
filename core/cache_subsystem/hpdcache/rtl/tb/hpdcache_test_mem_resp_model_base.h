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
 *  Description: Memory model for the HPDCACHE testbench
 */
#ifndef __HPDCACHE_TEST_MEM_RESP_MODEL_BASE_H__
#define __HPDCACHE_TEST_MEM_RESP_MODEL_BASE_H__

#include <systemc>
#include <map>
#include <iostream>
#include <scv.h>
#include "hpdcache_test_defs.h"
#include "mem_model.h"
#include "logger.h"

class hpdcache_test_mem_resp_model_base
{
public:

    struct segment_t {
        uint64_t base_addr;
        uint64_t end_addr;
        bool     error;

        segment_t(uint64_t base, uint64_t end, bool error) :
                base_addr(base), end_addr(end), error(error) {};
    };

    struct excl_reservation_buf_t
    {
        bool     valid;
        uint64_t base_addr;
        uint64_t end_addr;
    };

    using hpdcache_mem_atomic_e  = hpdcache_test_transaction_mem_req::hpdcache_mem_atomic_e;
    using hpdcache_mem_command_e = hpdcache_test_transaction_mem_req::hpdcache_mem_command_e;

protected:

    class mem_write_req_flit_t
    {
        public:

        uint64_t addr;
        uint32_t len;
        uint32_t size;
        uint32_t id;
        uint32_t command;
        uint32_t atomic;
        bool     cacheable;

        const std::string to_string() const
        {
            std::stringstream os;

            os << "MEM_WRITE"
               << " / ADDR = 0x" << std::hex << addr << std::dec
               << " / LEN = 0d" << std::dec << len << std::dec
               << " / ID = 0x" << std::hex << id << std::dec;
            return os.str();
        }

        friend std::ostream& operator<< (std::ostream& os, const mem_write_req_flit_t& r)
        {
            os << r.to_string();
            return os;
        }
    };

    class mem_write_req_data_flit_t
    {
        public:

        sc_bv<HPDCACHE_MEM_DATA_WIDTH>   data;
        sc_bv<HPDCACHE_MEM_DATA_WIDTH/8> be;
        bool                             last;

        const std::string to_string() const
        {
            std::stringstream os;

            os << "MEM_WRITE_DATA"
               << " / DATA = 0x" << std::hex << data << std::dec
               << " / BE = 0x" << std::hex << be << std::dec
               << (last ? " / LAST" : "");
            return os.str();
        }

        friend std::ostream& operator<< (std::ostream& os, const mem_write_req_data_flit_t& r)
        {
            os << r.to_string();
            return os;
        }
    };

    sc_fifo<hpdcache_test_transaction_mem_read_resp>  read_resp_fifo;
    sc_fifo<mem_write_req_flit_t>                     write_req_fifo;
    sc_fifo<mem_write_req_data_flit_t>                write_req_data_fifo;
    sc_fifo<hpdcache_test_transaction_mem_write_resp> write_resp_fifo;

    std::vector<segment_t> errorsegs;
    mem_model *memory_m;
    excl_reservation_buf_t excl_buf_m[1 << HPDCACHE_MEM_ID_WIDTH];

    scv_smart_ptr<int> ra_ready_delay;
    scv_smart_ptr<int> rd_valid_delay;
    scv_smart_ptr<int> wa_ready_delay;
    scv_smart_ptr<int> wd_ready_delay;
    scv_smart_ptr<int> wb_valid_delay;

    static constexpr unsigned int MEM_NOC_DATA_WORDS = HPDCACHE_MEM_DATA_WIDTH/64;

    bool check_verbosity(sc_core::sc_verbosity verbosity)
    {
        return (sc_core::sc_report_handler::get_verbosity_level() >= verbosity);
    }

public:

    hpdcache_test_mem_resp_model_base(const std::string &nm) :
            read_resp_fifo(HPDCACHE_MSHR_SETS*HPDCACHE_MSHR_WAYS),
            write_resp_fifo(HPDCACHE_WBUF_DIR_ENTRIES)

    {
        std::string mem_model_name;
        mem_model_name = mem_model_name + "_" + nm;
        memory_m = new mem_model(mem_model_name.c_str(), mem_model::MEM_MODEL_INIT_RANDOM);

        // set default values for delay distributions
        scv_bag<pair<int, int>> ra_delay_distribution;
        ra_delay_distribution.push(pair<int,int>(0,  2), 90);
        ra_delay_distribution.push(pair<int,int>(3,  8),  8);
        ra_delay_distribution.push(pair<int,int>(9, 32),  2);
        ra_ready_delay->set_mode(ra_delay_distribution);

        scv_bag<pair<int, int>> rd_delay_distribution;
        rd_delay_distribution.push(pair<int,int>(0,  2),  8);
        rd_delay_distribution.push(pair<int,int>(3,  8), 90);
        rd_delay_distribution.push(pair<int,int>(9, 64),  2);
        rd_valid_delay->set_mode(rd_delay_distribution);

        scv_bag<pair<int, int>> wa_delay_distribution;
        wa_delay_distribution.push(pair<int,int>(0,  2), 90);
        wa_delay_distribution.push(pair<int,int>(3,  8),  8);
        wa_delay_distribution.push(pair<int,int>(9, 32),  2);
        wa_ready_delay->set_mode(wa_delay_distribution);

        scv_bag<pair<int, int>> wd_delay_distribution;
        wd_delay_distribution.push(pair<int,int>(0,  2), 90);
        wd_delay_distribution.push(pair<int,int>(3,  8),  8);
        wd_delay_distribution.push(pair<int,int>(9, 32),  2);
        wd_ready_delay->set_mode(wd_delay_distribution);

        scv_bag<pair<int, int>> wb_delay_distribution;
        wb_delay_distribution.push(pair<int,int>(0,  2),  8);
        wb_delay_distribution.push(pair<int,int>(3,  8), 90);
        wb_delay_distribution.push(pair<int,int>(9, 64),  2);
        wb_valid_delay->set_mode(wb_delay_distribution);
    }

    ~hpdcache_test_mem_resp_model_base()
    {
        delete memory_m;
    }

    void add_error_segment(const segment_t& s)
    {
        errorsegs.push_back(s);
    }

    void set_ra_ready_delay_distribution(scv_bag<pair<int, int>> &dist)
    {
        ra_ready_delay->set_mode(dist);
    }

    scv_smart_ptr<int> get_ra_ready_delay_distribution()
    {
        return ra_ready_delay;
    }

    void set_rd_valid_delay_distribution(scv_bag<pair<int, int>> &dist)
    {
        rd_valid_delay->set_mode(dist);
    }

    scv_smart_ptr<int> get_rd_valid_delay_distribution()
    {
        return rd_valid_delay;
    }

    void set_wa_ready_delay_distribution(scv_bag<pair<int, int>> &dist)
    {
        wa_ready_delay->set_mode(dist);
    }

    scv_smart_ptr<int> get_wa_ready_delay_distribution()
    {
        return wa_ready_delay;
    }

    void set_wd_ready_delay_distribution(scv_bag<pair<int, int>> &dist)
    {
        wd_ready_delay->set_mode(dist);
    }

    scv_smart_ptr<int> get_wd_ready_delay_distribution()
    {
        return wd_ready_delay;
    }

    void set_wb_valid_delay_distribution(scv_bag<pair<int, int>> &dist)
    {
        wb_valid_delay->set_mode(dist);
    }

    scv_smart_ptr<int> get_wb_valid_delay_distribution()
    {
        return wb_valid_delay;
    }

    bool within_region(uint64_t base0, uint64_t end0, uint64_t base1, uint64_t end1)
    {
        if (end0  <= base1) return false;
        if (base0 >=  end1) return false;
        return true;
    }

    bool within_error_region(uint64_t base, uint64_t end)
    {
        for (const segment_t& s : errorsegs) {
            if (within_region(s.base_addr, s.end_addr, base, end)) {
                return s.error;
            }
        }
        return false;
    }

    uint64_t compute_amo(hpdcache_test_transaction_mem_req::hpdcache_mem_atomic_e atop,
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

        switch (atop) {
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_ADD :
                return ld_data +  st_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_CLR :
                return ld_data & ~st_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_SET :
                return ld_data |  st_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_EOR :
                return ld_data ^  st_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_SMAX:
                return smax ? ld_data : st_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_UMAX:
                return umax ? ld_data : st_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_SMIN:
                return smax ? st_data : ld_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_UMIN:
                return umax ? st_data : ld_data;
            case hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_SWAP:
                return st_data;
        }

        sc_assert(false && "unknown atomic operation");
        return 0;
    }
};

#endif /* __HPDCACHE_TEST_MEM_RESP_MODEL_BASE_H__ */
