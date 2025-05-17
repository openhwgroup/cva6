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
 *  Description: Base class definition of the HPDCACHE test sequence
 */
#ifndef __HPDCACHE_TEST_SEQUENCE_H__
#define __HPDCACHE_TEST_SEQUENCE_H__

#include <systemc>
#include "scv.h"
#include "hpdcache_test_defs.h"
#include "sequence.h"
#include "hpdcache_test_transaction.h"
#include "hpdcache_test_mem_resp_model_base.h"

class hpdcache_test_sequence : public Sequence
{
    const int HPDCACHE_REQ_MAX_TRANS_ID = 1 << HPDCACHE_REQ_TRANS_ID_WIDTH;

public:

    hpdcache_test_sequence(sc_core::sc_module_name nm, std::string seq_name) :
          Sequence                  (nm)
        , name                      (seq_name)
        , max_transactions          (100)
        , segptr                    ("segptr")
        , seg_distribution          ("seg_distribution")
        , delay                     ("delay")
        , delay_distribution        ("delay_distribution")
        , amo_size                  ("amo_size")
        , amo_size_distribution     ("amo_size_distribution")
        , amo_sc_do                 ("amo_sc_do")
        , amo_sc_do_distribution    ("amo_sc_do_distribution")
        , op                        ("op")
        , op_distribution           ("op_distribution")
        , op_amo                    ("op_amo")
        , op_amo_distribution       ("op_amo_distribution")
        , wr_policy                 ("wr_policy")
        , wr_policy_distribution    ("wr_policy_distribution")
    {
        std::cout << "Building " << nm << std::endl;
    }

    class hpdcache_test_memory_segment
    {
    public:
        enum wr_policy_e {
            WR_POLICY_AUTO   = 0,
            WR_POLICY_WB     = 1,
            WR_POLICY_WT     = 2,
            WR_POLICY_RANDOM = 3
        };

    private:
        sc_bv<HPDCACHE_PA_WIDTH> base;
        sc_bv<HPDCACHE_PA_WIDTH> length;
        bool                     uncached;
        bool                     amo_supported;
        wr_policy_e              wr_policy_hint;

    public:
        hpdcache_test_memory_segment() :
              base                      (0)
            , length                    (0)
            , uncached                  (false)
            , amo_supported             (false)
            , wr_policy_hint            (WR_POLICY_AUTO)
        { /* empty */ }

        const uint64_t get_base() const
        {
            return base.to_uint64();
        }

        const uint64_t get_length() const
        {
            return length.to_uint64();
        }

        const uint64_t get_end() const
        {
            return base.to_uint64() + (length.to_uint64() - 1ULL);
        }

        const bool is_uncached() const
        {
            return uncached;
        }

        const bool is_amo_supported() const
        {
            return amo_supported;
        }

        const wr_policy_e get_wr_policy_hint() const
        {
            return wr_policy_hint;
        }

        void set_base(uint64_t base)
        {
            this->base = sc_bv<HPDCACHE_PA_WIDTH>(base);
        }

        void set_length(uint64_t length)
        {
            this->length = sc_bv<HPDCACHE_PA_WIDTH>(length);
        }

        void set_uncached(bool uncached)
        {
            this->uncached = uncached;
        }

        void set_amo_supported(bool amo_supported)
        {
            this->amo_supported = amo_supported;
        }

        const void set_wr_policy_hint(wr_policy_e wr_policy_hint)
        {
            this->wr_policy_hint = wr_policy_hint;
        }
    };

    bool is_available_id()
    {
        return (ids.size() < HPDCACHE_REQ_MAX_TRANS_ID);
    }

    unsigned int allocate_id()
    {
        unsigned int id;

        assert (is_available_id());

        id = rand() % HPDCACHE_REQ_MAX_TRANS_ID;
        for (;;) {
            auto it = std::find(ids.begin(), ids.end(), id);
            if (it == ids.end()) {
                ids.insert(it, id);
                break;
            }
            id = (id + 1) % HPDCACHE_REQ_MAX_TRANS_ID;
        }
        return id;
    }

    void deallocate_id(unsigned int id)
    {
        auto it = std::find(ids.begin(), ids.end(), id);
        if (it != ids.end()) {
            ids.erase(it);
            return;
        }

        std::cout << "SEQ_ERROR: acknowledging an ID that is not currently used" << std::endl;
    }

    void set_max_transactions(size_t max_transactions)
    {
        this->max_transactions = max_transactions;
    }

    std::list<unsigned int>::const_iterator ids_cbegin()
    {
        return ids.cbegin();
    }

    std::list<unsigned int>::const_iterator ids_cend()
    {
        return ids.cend();
    }

    const std::list<unsigned int> &get_ids()
    {
        return ids;
    }

    size_t ids_size()
    {
        return ids.size();
    }

    void set_mem_resp_model(std::shared_ptr<hpdcache_test_mem_resp_model_base> p)
    {
        mem_resp_model = p;
    }

    std::shared_ptr<hpdcache_test_mem_resp_model_base> get_mem_resp_model()
    {
        return mem_resp_model;
    }

    void send_transaction(std::shared_ptr<hpdcache_test_transaction_req> t, int delay = 1)
    {
        // send transaction to the driver
        transaction_fifo_o->write(t);

        // wait and consume driver acknowledgement (this is blocking)
        transaction_ret_i.read();

        // release the previously used transaction object
        release_transaction<hpdcache_test_transaction_req>(t);

        // add some delay between two consecutive commands
        for (int i = 0; i < delay; i++) wait();
    }

    const std::string to_string() const
    {
        std::stringstream os;
        os << "Sequence " << name << " / Max Transactions = " << max_transactions << std::endl;
        return os.str();
    }

    friend std::ostream& operator<< (std::ostream& os,
                                     const hpdcache_test_sequence& seq)
    {
        os << seq.to_string();
        return os;
    }


protected:

    std::list<unsigned int> ids;
    std::string             name;
    size_t                  max_transactions;
    scv_smart_ptr<int>      segptr;
    scv_bag<int>            seg_distribution;
    scv_smart_ptr<int>      delay;
    scv_bag<pair<int, int>> delay_distribution;
    scv_smart_ptr<int>      amo_size;
    scv_bag<int>            amo_size_distribution;
    scv_smart_ptr<bool>     amo_sc_do;
    scv_bag<bool>           amo_sc_do_distribution;
    scv_smart_ptr<int>      op;
    scv_bag<int>            op_distribution;
    scv_smart_ptr<int>      op_amo;
    scv_bag<int>            op_amo_distribution;
    scv_smart_ptr<int>      wr_policy;
    scv_bag<int>            wr_policy_distribution;

    std::shared_ptr<hpdcache_test_mem_resp_model_base> mem_resp_model;
};

#endif // __HPDCACHE_TEST_SEQUENCE_H__
