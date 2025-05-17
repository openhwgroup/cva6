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
 *  Description: class definition of the HPDCACHE test driver
 */
#ifndef __HPDCACHE_TEST_DRIVER_H__
#define __HPDCACHE_TEST_DRIVER_H__

#include <systemc>
#include <string>
#include <verilated.h>
#include "logger.h"
#include "driver.h"
#include "hpdcache_test_transaction.h"
#include "hpdcache_test_defs.h"

using namespace sc_core;
using namespace sc_dt;

class hpdcache_test_driver : public Driver
{
public:
    sc_out <bool>                                core_req_valid_o;
    sc_in  <bool>                                core_req_ready_i;
    sc_out <sc_bv<HPDCACHE_CORE_REQ_WIDTH> >     core_req_o;
    sc_out <bool>                                core_req_abort_o;
    sc_out <uint64_t>                            core_req_tag_o;
    sc_out <uint32_t>                            core_req_pma_o;

    sc_in  <bool>                                core_rsp_valid_i;
    sc_in  <sc_bv<HPDCACHE_CORE_RSP_WIDTH> >     core_rsp_i;

    sc_fifo_out<hpdcache_test_transaction_req>   sb_core_req_o;
    sc_fifo_out<hpdcache_test_transaction_resp>  sb_core_resp_o;

    hpdcache_test_driver(sc_core::sc_module_name nm) : Driver(nm)
    {
        SC_THREAD(drive_request);
        sensitive << clk_i.pos();

        SC_THREAD(monitor_response);
        sensitive << clk_i.neg();
    };

private:

#if SC_VERSION_MAJOR < 3
    SC_HAS_PROCESS(hpdcache_test_driver);
#endif

    typedef std::shared_ptr<hpdcache_test_transaction_req> transaction_ptr;

    static inline uint64_t core_get_req_tag(const transaction_ptr &t)
    {
        sc_bv<HPDCACHE_TAG_WIDTH> ret;
        ret = t->req_addr.range(HPDCACHE_PA_WIDTH - 1, HPDCACHE_ADDR_OFFSET_WIDTH);
        return ret.to_uint64();
    }

    static inline uint32_t core_get_req_pma(const transaction_ptr &t)
    {
        int ret = 0;
        if (t->is_wr_policy_auto()) ret |= (0x1 << 0);
        if (t->is_wr_policy_wb())   ret |= (0x1 << 1);
        if (t->is_wr_policy_wt())   ret |= (0x1 << 2);
        if (t->req_io)              ret |= (0x1 << 3);
        if (t->req_uncacheable)     ret |= (0x1 << 4);
        return ret;
    }

    static sc_bv<HPDCACHE_CORE_REQ_WIDTH> core_req_to_bv(const transaction_ptr &t)
    {
        const int unsigned PMA_POS = 0;
        const int unsigned TAG_POS = PMA_POS + HPDCACHE_REQ_PMA_WIDTH;
        const int unsigned PHYS_INDEXED_POS = TAG_POS + HPDCACHE_TAG_WIDTH;
        const int unsigned NEED_RSP_POS = PHYS_INDEXED_POS + HPDCACHE_REQ_PHYS_INDEXED_WIDTH;
        const int unsigned TRANS_ID_POS = NEED_RSP_POS + HPDCACHE_REQ_NEED_RSP_WIDTH;
        const int unsigned SRC_ID_POS = TRANS_ID_POS + HPDCACHE_REQ_TRANS_ID_WIDTH;
        const int unsigned SIZE_POS = SRC_ID_POS + HPDCACHE_REQ_SRC_ID_WIDTH;
        const int unsigned BE_POS = SIZE_POS + HPDCACHE_REQ_SIZE_WIDTH;
        const int unsigned OP_POS = BE_POS + (HPDCACHE_REQ_DATA_WIDTH/8);
        const int unsigned WDATA_POS = OP_POS + HPDCACHE_REQ_OP_WIDTH;
        const int unsigned ADDR_POS = WDATA_POS + HPDCACHE_REQ_DATA_WIDTH;
        sc_bv<HPDCACHE_CORE_REQ_WIDTH> ret;

        ret.range(PMA_POS + HPDCACHE_REQ_PMA_WIDTH - 1, PMA_POS) =
            core_get_req_pma(t);
        ret.range(TAG_POS + HPDCACHE_TAG_WIDTH - 1, TAG_POS) =
            core_get_req_tag(t);
        ret.range(PHYS_INDEXED_POS + HPDCACHE_REQ_PHYS_INDEXED_WIDTH - 1, PHYS_INDEXED_POS) =
            t->req_phys_indexed ? 1 : 0;
        ret.range(NEED_RSP_POS + HPDCACHE_REQ_NEED_RSP_WIDTH - 1, NEED_RSP_POS) =
            t->req_need_rsp ? 1 : 0;
        ret.range(TRANS_ID_POS + HPDCACHE_REQ_TRANS_ID_WIDTH - 1, TRANS_ID_POS) =
            t->req_tid;
        ret.range(SRC_ID_POS + HPDCACHE_REQ_SRC_ID_WIDTH - 1, SRC_ID_POS) =
            t->req_sid;
        ret.range(SIZE_POS + HPDCACHE_REQ_SIZE_WIDTH - 1, SIZE_POS) =
            t->req_size;
        ret.range(BE_POS + (HPDCACHE_REQ_DATA_WIDTH/8) - 1, BE_POS) =
            t->req_be;
        ret.range(OP_POS + HPDCACHE_REQ_OP_WIDTH - 1, OP_POS) =
            t->req_op;
        ret.range(WDATA_POS + HPDCACHE_REQ_DATA_WIDTH - 1, WDATA_POS) =
            t->req_wdata;
        ret.range(ADDR_POS + HPDCACHE_ADDR_OFFSET_WIDTH - 1, ADDR_POS) =
            t->req_addr.range(HPDCACHE_ADDR_OFFSET_WIDTH, 0);

        return ret;
    }

    static void core_resp_to_struct(hpdcache_test_transaction_resp &resp, const sc_bv<HPDCACHE_CORE_RSP_WIDTH> &bv)
    {
        const int unsigned ABORTED_POS = 0;
        const int unsigned ERROR_POS = ABORTED_POS + HPDCACHE_RSP_ABORTED_WIDTH;
        const int unsigned TRANS_ID_POS = ERROR_POS + HPDCACHE_RSP_ERROR_WIDTH;
        const int unsigned SRC_ID_POS = TRANS_ID_POS + HPDCACHE_REQ_TRANS_ID_WIDTH;
        const int unsigned RDATA_POS = SRC_ID_POS + HPDCACHE_REQ_SRC_ID_WIDTH;

        resp.rsp_aborted = (bv.range(ABORTED_POS + HPDCACHE_RSP_ABORTED_WIDTH  - 1, ABORTED_POS).to_uint() > 0);
        resp.rsp_error = (bv.range(ERROR_POS + HPDCACHE_RSP_ERROR_WIDTH - 1, ERROR_POS).to_uint() > 0);
        resp.rsp_tid = bv.range(TRANS_ID_POS + HPDCACHE_REQ_TRANS_ID_WIDTH - 1, TRANS_ID_POS);
        resp.rsp_sid = bv.range(SRC_ID_POS + HPDCACHE_REQ_SRC_ID_WIDTH - 1, SRC_ID_POS);
        resp.rsp_rdata = bv.range(RDATA_POS + HPDCACHE_REQ_DATA_WIDTH - 1, RDATA_POS);
    }


    void drive_request()
    {
        transaction_ptr t;
        for (;;) {
            t = std::dynamic_pointer_cast<hpdcache_test_transaction_req>(
                    transaction_fifo_i.read());

            if (t == nullptr) break;

            core_req_valid_o.write(true);
            core_req_o.write(core_req_to_bv(t));
            do wait(); while (!core_req_ready_i.read());
            core_req_valid_o.write(false);

            // send the tag
            core_req_tag_o.write(core_get_req_tag(t));
            core_req_pma_o.write(core_get_req_pma(t));
            core_req_abort_o.write(t->is_aborted());

            transaction_ret_o.write(t->get_id());

            //  send request to the scoreboard
            sb_core_req_o.write(*t);
        }

        // FIXME : I should find a better way to know when all transactions
        // have been completed. Otherwise, finish the simulation in a different
        // place (e.g. the scoreboard that knows all pending transactions)
        for (int i = 0; i < 10000; i++) {
            wait();
        }

        Verilated::gotFinish(true);
    }

    void drive_tag()
    {
        for (;;) {

            wait();

        }
    }

    void monitor_response()
    {
        for (;;) {
            wait();

            if (core_rsp_valid_i.read()) {
                hpdcache_test_transaction_resp resp;
                core_resp_to_struct(resp, core_rsp_i.read());

                //  send response to the scoreboard
                sb_core_resp_o.write(resp);
            }
        }
    }
};

#endif // __HPDCACHE_TEST_DRIVER_H__
