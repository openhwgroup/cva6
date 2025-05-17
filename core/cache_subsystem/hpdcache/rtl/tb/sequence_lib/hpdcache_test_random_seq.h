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
 *  Description: Class definition of the HPDCACHE test random sequence
 */
#ifndef __HPDCACHE_TEST_RANDOM_SEQ_H__
#define __HPDCACHE_TEST_RANDOM_SEQ_H__

#include <systemc>
#include "scv.h"
#include "hpdcache_test_defs.h"
#include "hpdcache_test_sequence.h"

#define HPDCACHE_TEST_SEQUENCE_ENABLE_ERROR_SEGMENTS 1

class hpdcache_test_random_seq : public hpdcache_test_sequence
{
public:

    hpdcache_test_random_seq(sc_core::sc_module_name nm) : hpdcache_test_sequence(nm, "random_seq")
    {
        SC_THREAD(run);
        sensitive << clk_i.pos();

        seg[0].set_base           (0x00000000ULL);
        seg[0].set_length         (0x00004000ULL);
        seg[0].set_uncached       (false);
        seg[0].set_amo_supported  (true);
        seg[0].set_wr_policy_hint (hpdcache_test_memory_segment::WR_POLICY_RANDOM);

        seg[1].set_base           (0x40004000ULL);
        seg[1].set_length         (0x00004000ULL);
        seg[1].set_uncached       (false);
        seg[1].set_amo_supported  (true);
        seg[1].set_wr_policy_hint (hpdcache_test_memory_segment::WR_POLICY_WB);

        seg[2].set_base           (0x80008000ULL);
        seg[2].set_length         (0x00004000ULL);
        seg[2].set_uncached       (false);
        seg[2].set_wr_policy_hint (hpdcache_test_memory_segment::WR_POLICY_WT);

        /*FIXME this is a workaround because currently the WB policy does not support AMOs*/
#if CONF_HPDCACHE_WT_ENABLE
        seg[2].set_amo_supported  (true);
#else
        seg[2].set_amo_supported  (false);
#endif

        seg[3].set_base           (0xC000C000ULL);
        seg[3].set_length         (0x00004000ULL);
        seg[3].set_uncached       (true);
        seg[3].set_amo_supported  (true);
        seg[3].set_wr_policy_hint (hpdcache_test_memory_segment::WR_POLICY_AUTO);

        hpdcache_test_sequence::seg_distribution.push(0, 33);
        hpdcache_test_sequence::seg_distribution.push(1, 33);
        hpdcache_test_sequence::seg_distribution.push(2, 33);
        hpdcache_test_sequence::seg_distribution.push(3,  1);
        hpdcache_test_sequence::segptr->set_mode(seg_distribution);

        hpdcache_test_sequence::delay_distribution.push(pair<int,int>(0,  0), 80);
        hpdcache_test_sequence::delay_distribution.push(pair<int,int>(1,  4), 18);
        hpdcache_test_sequence::delay_distribution.push(pair<int,int>(5, 20),  2);
        hpdcache_test_sequence::delay->set_mode(delay_distribution);

        hpdcache_test_sequence::amo_sc_do_distribution.push(false, 25);
        hpdcache_test_sequence::amo_sc_do_distribution.push(true,  75);
        hpdcache_test_sequence::amo_sc_do->set_mode(amo_sc_do_distribution);

        hpdcache_test_sequence::wr_policy_distribution.push(hpdcache_test_transaction_req::HPDCACHE_WR_POLICY_AUTO,        80);
        hpdcache_test_sequence::wr_policy_distribution.push(hpdcache_test_transaction_req::HPDCACHE_WR_POLICY_WB,          10);
        hpdcache_test_sequence::wr_policy_distribution.push(hpdcache_test_transaction_req::HPDCACHE_WR_POLICY_WT,          10);
        hpdcache_test_sequence::wr_policy->set_mode(wr_policy_distribution);

        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_LOAD,                    400);
        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_STORE,                   350);
        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FENCE,                10);
        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_PREFETCH,             10);
//        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_INVAL_NLINE,          15);
//        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_INVAL_ALL,            15);
        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_NLINE,          10);
        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_ALL,             1);
        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE,    10);
        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL,       1);
        hpdcache_test_sequence::op->set_mode(op_distribution);

        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_LOAD,                 400);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_STORE,                350);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FENCE,             10);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_PREFETCH,          10);
//        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_INVAL_NLINE,       15);
//        hpdcache_test_sequence::op_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_INVAL_ALL,         15);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_NLINE,       10);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_ALL,          1);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE, 10);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL,    1);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_LR,                 4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_SC,                 4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_SWAP,               4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_ADD,                4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_AND,                4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_OR,                 4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_XOR,                4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MAX,                4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MAXU,               4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MIN,                4);
        hpdcache_test_sequence::op_amo_distribution.push(hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_MINU,               4);
        hpdcache_test_sequence::op_amo->set_mode(op_amo_distribution);
    }

private:
    hpdcache_test_sequence::hpdcache_test_memory_segment seg[4];
    scv_smart_ptr<sc_bv<HPDCACHE_REQ_DATA_WIDTH> > data;
    scv_smart_ptr<sc_bv<HPDCACHE_REQ_DATA_WIDTH> > size;
    const unsigned int HPDCACHE_REQ_DATA_BYTES = HPDCACHE_REQ_DATA_WIDTH/8;

#if SC_VERSION_MAJOR < 3
    SC_HAS_PROCESS(hpdcache_test_random_seq);
#endif

    inline sc_bv<HPDCACHE_REQ_DATA_WIDTH> create_random_data()
    {
        data->next();
        return data->read();
    }

    inline uint32_t create_random_size(bool is_amo)
    {
        if (!is_amo) size->keep_only(0, 3);
        else         size->keep_only(2, 3);

        size->next();
        return size->read().to_uint();
    }

    std::shared_ptr<hpdcache_test_transaction_req> create_random_transaction()
    {
        std::shared_ptr<hpdcache_test_transaction_req> t;

        scv_smart_ptr<uint64_t> addr("addr");

        while (!is_available_id()) wait();

        hpdcache_test_sequence::segptr->next();
        int segn = segptr->read();

        hpdcache_test_memory_segment::wr_policy_e seg_wr_policy =
            seg[segn].get_wr_policy_hint();

        bool seg_amo_supported =
            seg[segn].is_amo_supported();
        bool seg_wr_policy_random =
            (seg_wr_policy == hpdcache_test_memory_segment::WR_POLICY_RANDOM);

        addr->next();

        t = acquire_transaction<hpdcache_test_transaction_req>();

        //  Select operation
        if (seg_amo_supported) {
            hpdcache_test_sequence::op_amo->next();
            t->req_op = op_amo->read();
        } else {
            hpdcache_test_sequence::op->next();
            t->req_op = op->read();
        }

        t->req_wdata        = create_random_data();
        t->req_sid          = 0;
        t->req_tid          = allocate_id();
        t->req_abort        = false;
        t->req_phys_indexed = false;

        //  Select write policy
        if (seg_wr_policy_random) {
            wr_policy->next();
            t->req_wr_policy_hint =
                    (hpdcache_test_transaction_req::hpdcache_wr_policy_hint_e)wr_policy->read();
        } else if (seg_wr_policy == hpdcache_test_memory_segment::WR_POLICY_WB) {
            t->req_wr_policy_hint = hpdcache_test_transaction_req::HPDCACHE_WR_POLICY_WB;
        } else if (seg_wr_policy == hpdcache_test_memory_segment::WR_POLICY_WT) {
            t->req_wr_policy_hint = hpdcache_test_transaction_req::HPDCACHE_WR_POLICY_WT;
        } else {
            t->req_wr_policy_hint = hpdcache_test_transaction_req::HPDCACHE_WR_POLICY_AUTO;
        }

        //  Select address and size
        uint32_t sz = create_random_size(
                t->is_amo() ||
                t->is_amo_sc() ||
                t->is_amo_lr());
        uint64_t base    = seg[segn].get_base();
        uint64_t length  = seg[segn].get_length();
        uint32_t bytes   = 1 << sz;
        uint64_t address = ((base + (addr->read() % length)) / bytes) * bytes;

        t->req_addr = address;
        if (t->is_cmo()) {
            t->req_be          = 0;
            t->req_size        = 0;
            t->req_uncacheable = false;
            t->req_need_rsp    = true;
        } else {
            uint32_t offset = address % HPDCACHE_REQ_DATA_BYTES;
            t->req_be          = ((1UL << bytes) - 1) << offset;
            t->req_size        = sz;
            t->req_uncacheable = seg[segptr->read()].is_uncached() ? 1 : 0;
            t->req_need_rsp    = true;
        }

        return t;
    }

    std::shared_ptr<hpdcache_test_transaction_req> create_sc_transaction(uint64_t addr, bool uncacheable)
    {
        std::shared_ptr<hpdcache_test_transaction_req> t;

        while (!is_available_id()) wait();

        hpdcache_test_sequence::segptr->next();

        uint32_t sz      = create_random_size(true);
        uint32_t bytes   = 1 << sz;
        uint64_t address = (addr / bytes) * bytes;
        uint32_t offset  = address % HPDCACHE_REQ_DATA_BYTES;

        t = acquire_transaction<hpdcache_test_transaction_req>();
        t->req_op          = hpdcache_test_transaction_req::HPDCACHE_REQ_AMO_SC;
        t->req_wdata       = create_random_data();
        t->req_sid         = 0;
        t->req_tid         = allocate_id();
        t->req_addr        = address;
        t->req_be          = ((1UL << bytes) - 1) << offset;
        t->req_size        = sz;
        t->req_uncacheable = uncacheable;
        t->req_need_rsp    = true;

        return t;
    }

    void run()
    {

#if HPDCACHE_TEST_SEQUENCE_ENABLE_ERROR_SEGMENTS
        if (hpdcache_test_sequence::mem_resp_model) {
            hpdcache_test_sequence::mem_resp_model->add_error_segment(
                hpdcache_test_mem_resp_model_base::segment_t(
                    0x00000000ULL, 0x00000200ULL, true
                )
            );
            hpdcache_test_sequence::mem_resp_model->add_error_segment(
                hpdcache_test_mem_resp_model_base::segment_t(
                    0x40004000ULL, 0x40004200ULL, true
                )
            );
            hpdcache_test_sequence::mem_resp_model->add_error_segment(
                hpdcache_test_mem_resp_model_base::segment_t(
                    0xC000C000ULL, 0xC000C200ULL, true
                )
            );
        }
#endif

        while (rst_ni == 0) wait();

        wait();

        scv_smart_ptr<int> lrsc_inbetween_instrs;
        lrsc_inbetween_instrs->keep_only(0, 10);
        lrsc_inbetween_instrs->next();

        delay->next();
        for (size_t n = 0; n < this->max_transactions; n++) {
            std::shared_ptr<hpdcache_test_transaction_req> t;
            t = create_random_transaction();

            if (t->is_amo_lr()) {
                hpdcache_test_transaction_req prev_lr = *t;
                send_transaction(t, delay->read());
                delay->next();

                amo_sc_do->next();
                if (amo_sc_do->read()) {
                    for (int i = 0; i < lrsc_inbetween_instrs.read(); i++) {
                        t = create_random_transaction();
                        send_transaction(t, delay->read());
                        delay->next();
                    }

                    t = create_sc_transaction(prev_lr.req_addr.to_uint64(), prev_lr.req_uncacheable);
                    send_transaction(t, delay->read());
                    delay->next();
                }

                continue;
            }
            send_transaction(t, delay->read());
            delay->next();
        }

        //  ask the driver to stop
        transaction_fifo_o->write(nullptr);
    }
};

#endif // __HPDCACHE_TEST_RANDOM_SEQ_H__
