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
 *  Description: Class definitions for hpdcache_test transactions
 */
#ifndef __HPDCACHE_TEST_TRANSACTION_H__
#define __HPDCACHE_TEST_TRANSACTION_H__

#include <sstream>
#include <verilated.h>
#include "transaction.h"
#include "hpdcache_test_defs.h"

using namespace sc_dt;

class hpdcache_test_transaction_req : public Transaction
{
public:
    enum hpdcache_req_op_e {
        HPDCACHE_REQ_LOAD                  = 0x00,
        HPDCACHE_REQ_STORE                 = 0x01,
        // RESERVED                        = 0x02,
        // RESERVED                        = 0x03,
        HPDCACHE_REQ_AMO_LR                = 0x04,
        HPDCACHE_REQ_AMO_SC                = 0x05,
        HPDCACHE_REQ_AMO_SWAP              = 0x06,
        HPDCACHE_REQ_AMO_ADD               = 0x07,
        HPDCACHE_REQ_AMO_AND               = 0x08,
        HPDCACHE_REQ_AMO_OR                = 0x09,
        HPDCACHE_REQ_AMO_XOR               = 0x0a,
        HPDCACHE_REQ_AMO_MAX               = 0x0b,
        HPDCACHE_REQ_AMO_MAXU              = 0x0c,
        HPDCACHE_REQ_AMO_MIN               = 0x0d,
        HPDCACHE_REQ_AMO_MINU              = 0x0e,
        // RESERVED                        = 0x0f,
        HPDCACHE_REQ_CMO_FENCE             = 0x10,
        HPDCACHE_REQ_CMO_PREFETCH          = 0x11,
        HPDCACHE_REQ_CMO_INVAL_NLINE       = 0x12,
        HPDCACHE_REQ_CMO_INVAL_ALL         = 0x13,
        HPDCACHE_REQ_CMO_FLUSH_NLINE       = 0x14,
        HPDCACHE_REQ_CMO_FLUSH_ALL         = 0x15,
        HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE = 0x16,
        HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL   = 0x17
    };

    enum hpdcache_wr_policy_hint_e {
        HPDCACHE_WR_POLICY_AUTO           = 0b001,
        HPDCACHE_WR_POLICY_WB             = 0b010,
        HPDCACHE_WR_POLICY_WT             = 0b100
    };

    typedef std::shared_ptr<hpdcache_test_transaction_req> transaction_ptr;

    //  request
    sc_bv<HPDCACHE_PA_WIDTH>           req_addr;
    sc_bv<HPDCACHE_REQ_DATA_WIDTH>     req_wdata;
    sc_bv<HPDCACHE_REQ_OP_WIDTH>       req_op;
    sc_bv<HPDCACHE_REQ_DATA_WIDTH/8>   req_be;
    sc_bv<HPDCACHE_REQ_SIZE_WIDTH>     req_size;
    sc_bv<HPDCACHE_REQ_SRC_ID_WIDTH>   req_sid;
    sc_bv<HPDCACHE_REQ_TRANS_ID_WIDTH> req_tid;
    bool                               req_need_rsp;
    bool                               req_phys_indexed;
    bool                               req_uncacheable;
    bool                               req_io;
    hpdcache_wr_policy_hint_e          req_wr_policy_hint;
    bool                               req_abort;

    hpdcache_test_transaction_req()
    {
        req_addr           = 0;
        req_wdata          = 0;
        req_op             = 0;
        req_be             = 0;
        req_size           = 0;
        req_sid            = 0;
        req_tid            = 0;
        req_need_rsp       = false;
        req_phys_indexed   = false;
        req_uncacheable    = false;
        req_io             = false;
        req_wr_policy_hint = HPDCACHE_WR_POLICY_AUTO;
        req_abort          = false;
    }

    bool is_aborted() const
    {
        return req_abort;
    }

    bool is_uncacheable() const
    {
        return req_uncacheable;
    }

    bool is_io() const
    {
        return req_io;
    }

    bool is_wr_policy_wb() const
    {
        return (req_wr_policy_hint == HPDCACHE_WR_POLICY_WB);
    }

    bool is_wr_policy_wt() const
    {
        return (req_wr_policy_hint == HPDCACHE_WR_POLICY_WT);
    }

    bool is_wr_policy_auto() const
    {
        return (req_wr_policy_hint == HPDCACHE_WR_POLICY_AUTO);
    }

    bool is_load() const
    {
        return (req_op.to_uint() == HPDCACHE_REQ_LOAD);
    }

    bool is_store() const
    {
        return (req_op.to_uint() == HPDCACHE_REQ_STORE);
    }

    bool is_amo() const
    {
        unsigned op = this->req_op.to_uint();
        return ((op == HPDCACHE_REQ_AMO_SWAP) ||
                (op == HPDCACHE_REQ_AMO_ADD)  ||
                (op == HPDCACHE_REQ_AMO_AND)  ||
                (op == HPDCACHE_REQ_AMO_OR)   ||
                (op == HPDCACHE_REQ_AMO_XOR)  ||
                (op == HPDCACHE_REQ_AMO_MAX)  ||
                (op == HPDCACHE_REQ_AMO_MAXU) ||
                (op == HPDCACHE_REQ_AMO_MIN)  ||
                (op == HPDCACHE_REQ_AMO_MINU));
    }

    bool is_amo_lr() const
    {
        return (req_op.to_uint() == HPDCACHE_REQ_AMO_LR);
    }

    bool is_amo_sc() const
    {
        return (req_op.to_uint() == HPDCACHE_REQ_AMO_SC);
    }

    bool is_cmo() const
    {
        unsigned op = this->req_op.to_uint();
        return ((op == HPDCACHE_REQ_CMO_FENCE)             ||
                (op == HPDCACHE_REQ_CMO_PREFETCH)          ||
                (op == HPDCACHE_REQ_CMO_INVAL_NLINE)       ||
                (op == HPDCACHE_REQ_CMO_INVAL_ALL)         ||
                (op == HPDCACHE_REQ_CMO_FLUSH_NLINE)       ||
                (op == HPDCACHE_REQ_CMO_FLUSH_ALL)         ||
                (op == HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE) ||
                (op == HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL));
    }

    bool is_cmo_prefetch() const
    {
        unsigned op = this->req_op.to_uint();
        return (op == HPDCACHE_REQ_CMO_PREFETCH);
    }

    static const char* op_to_string(unsigned int op)
    {
        switch (op) {
            case HPDCACHE_REQ_LOAD                  : return "LOAD";
            case HPDCACHE_REQ_STORE                 : return "STORE";
            case HPDCACHE_REQ_AMO_LR                : return "LR";
            case HPDCACHE_REQ_AMO_SC                : return "SC";
            case HPDCACHE_REQ_AMO_SWAP              : return "AMO_SWAP";
            case HPDCACHE_REQ_AMO_ADD               : return "AMO_ADD";
            case HPDCACHE_REQ_AMO_AND               : return "AMO_AND";
            case HPDCACHE_REQ_AMO_OR                : return "AMO_OR";
            case HPDCACHE_REQ_AMO_XOR               : return "AMO_XOR";
            case HPDCACHE_REQ_AMO_MAX               : return "AMO_MAX";
            case HPDCACHE_REQ_AMO_MAXU              : return "AMO_MAXU";
            case HPDCACHE_REQ_AMO_MIN               : return "AMO_MIN";
            case HPDCACHE_REQ_AMO_MINU              : return "AMO_MINU";
            case HPDCACHE_REQ_CMO_FENCE             : return "CMO_FENCE";
            case HPDCACHE_REQ_CMO_PREFETCH          : return "CMO_PREFETCH";
            case HPDCACHE_REQ_CMO_INVAL_NLINE       : return "CMO_INVAL_NLINE";
            case HPDCACHE_REQ_CMO_INVAL_ALL         : return "CMO_INVAL_ALL";
            case HPDCACHE_REQ_CMO_FLUSH_NLINE       : return "CMO_FLUSH_NLINE";
            case HPDCACHE_REQ_CMO_FLUSH_ALL         : return "CMO_FLUSH_ALL";
            case HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE : return "CMO_FLUSH_INVAL_NLINE";
            case HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL   : return "CMO_FLUSH_INVAL_ALL";
            default                                 : return "UNKNOWN";
        }
    }

    static const char* cmo_to_string(unsigned int cmo)
    {
        switch (cmo) {
            case HPDCACHE_REQ_CMO_FENCE             : return "CMO_FENCE";
            case HPDCACHE_REQ_CMO_PREFETCH          : return "CMO_PREFETCH";
            case HPDCACHE_REQ_CMO_INVAL_NLINE       : return "CMO_INVAL_NLINE";
            case HPDCACHE_REQ_CMO_INVAL_ALL         : return "CMO_INVAL_ALL";
            case HPDCACHE_REQ_CMO_FLUSH_NLINE       : return "CMO_FLUSH_NLINE";
            case HPDCACHE_REQ_CMO_FLUSH_ALL         : return "CMO_FLUSH_ALL";
            case HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE : return "CMO_FLUSH_INVAL_NLINE";
            case HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL   : return "CMO_FLUSH_INVAL_ALL";
            default                                 : return "UNKNOWN";
        }
    }

    static const char* wr_policy_to_string(hpdcache_wr_policy_hint_e hint)
    {
        switch (hint) {
            case HPDCACHE_WR_POLICY_AUTO        : return "WR_POLICY_AUTO";
            case HPDCACHE_WR_POLICY_WB          : return "WR_POLICY_WB";
            case HPDCACHE_WR_POLICY_WT          : return "WR_POLICY_WT";
            default                             : return "UNKNOWN";
        }
    }

    const std::string to_string() const
    {
        std::stringstream os;
        bool contains_data = false;
        unsigned op = this->req_op.to_uint();

        switch (op) {
            case HPDCACHE_REQ_STORE:
            case HPDCACHE_REQ_AMO_SC:
            case HPDCACHE_REQ_AMO_SWAP:
            case HPDCACHE_REQ_AMO_ADD:
            case HPDCACHE_REQ_AMO_AND:
            case HPDCACHE_REQ_AMO_OR:
            case HPDCACHE_REQ_AMO_XOR:
            case HPDCACHE_REQ_AMO_MAX:
            case HPDCACHE_REQ_AMO_MAXU:
            case HPDCACHE_REQ_AMO_MIN:
            case HPDCACHE_REQ_AMO_MINU:
                contains_data = true;
                break;
        }

        os << "CORE_REQ / @ = " << req_addr.to_string(SC_HEX)
           << " / " << op_to_string(op)
           << " / SID = 0x" << std::hex << req_sid.to_uint() << std::dec
           << " / TID = 0x" << std::hex << req_tid.to_uint() << std::dec
           << " / WR_POLICY_HINT = " << wr_policy_to_string(req_wr_policy_hint);

        if (!is_cmo()) {
            os << (req_uncacheable ? " / UNCACHED" : " / CACHED")
               << " / SIZE = " << req_size.to_string(SC_HEX)
               << (req_need_rsp ? " / NEED_RSP" : " / NO NEED_RSP")
               << (req_phys_indexed ? " / PHYS_INDEXED" : " / VIRT_INDEXED");

            if (contains_data) {
               os << " / WDATA = " << req_wdata.to_string(SC_HEX)
                  << " / BE = "    << req_be.to_string(SC_HEX);
            }
        } else {
            os << " / " << cmo_to_string(op);
        }

        return os.str();
    }

    friend std::ostream& operator<< (std::ostream& os,
                                     const hpdcache_test_transaction_req& req)
    {
        os << req.to_string();
        return os;
    }
};

class hpdcache_test_transaction_resp : public Transaction
{
public:
    //  response
    sc_bv<HPDCACHE_REQ_DATA_WIDTH>     rsp_rdata;
    sc_bv<HPDCACHE_REQ_SRC_ID_WIDTH>   rsp_sid;
    sc_bv<HPDCACHE_REQ_TRANS_ID_WIDTH> rsp_tid;
    bool                               rsp_error;
    bool                               rsp_aborted;

    hpdcache_test_transaction_resp()
    {
        rsp_rdata       = 0;
        rsp_sid         = 0;
        rsp_tid         = 0;
        rsp_error       = 0;
        rsp_aborted     = 0;
    }

    typedef std::shared_ptr<hpdcache_test_transaction_resp> transaction_ptr;

    const std::string to_string() const
    {
        std::stringstream os;

        os << "CORE_RESP / RDATA = " << rsp_rdata.to_string(SC_HEX)
           << " / SID = 0x" << std::hex << rsp_sid.to_uint() << std::dec
           << " / TID = 0x" << std::hex << rsp_tid.to_uint() << std::dec
           << (rsp_error   ? " / ERROR"   : "")
           << (rsp_aborted ? " / ABORTED" : "");

        return os.str();
    }

    friend std::ostream& operator<< (std::ostream& os,
                                     const hpdcache_test_transaction_resp& resp)
    {
        os << resp.to_string();
        return os;
    }
};

class hpdcache_test_transaction_mem_req
{
public:

    uint64_t addr;
    uint32_t len;
    uint32_t size;
    uint32_t id;
    uint32_t command;
    uint32_t atomic;
    bool     cacheable;

    hpdcache_test_transaction_mem_req() :
            addr(0),
            len(0),
            size(0),
            id(0),
            command(0),
            atomic(0),
            cacheable(false)
    {

    }

    enum hpdcache_mem_command_e
    {
        HPDCACHE_MEM_READ     = 0x0,
        HPDCACHE_MEM_WRITE    = 0x1,
        HPDCACHE_MEM_ATOMIC   = 0x2
    };

    enum hpdcache_mem_atomic_e {
        HPDCACHE_MEM_ATOMIC_ADD  = 0x0,
        HPDCACHE_MEM_ATOMIC_CLR  = 0x1,
        HPDCACHE_MEM_ATOMIC_SET  = 0x2,
        HPDCACHE_MEM_ATOMIC_EOR  = 0x3,
        HPDCACHE_MEM_ATOMIC_SMAX = 0x4,
        HPDCACHE_MEM_ATOMIC_SMIN = 0x5,
        HPDCACHE_MEM_ATOMIC_UMAX = 0x6,
        HPDCACHE_MEM_ATOMIC_UMIN = 0x7,
        HPDCACHE_MEM_ATOMIC_SWAP = 0x8,
        HPDCACHE_MEM_ATOMIC_LDEX = 0xc,
        HPDCACHE_MEM_ATOMIC_STEX = 0xd
    };

    bool is_amo() const
    {
        return ((command == hpdcache_mem_command_e::HPDCACHE_MEM_ATOMIC) &&
                (atomic  !=  hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_STEX) &&
                (atomic  !=  hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_LDEX));
    }

    bool is_stex() const
    {
        return ((command == hpdcache_mem_command_e::HPDCACHE_MEM_ATOMIC) &&
                (atomic  ==  hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_STEX));
    }

    bool is_ldex() const
    {
        return ((command == hpdcache_mem_command_e::HPDCACHE_MEM_ATOMIC) &&
                (atomic  ==  hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_LDEX));
    }

    static const char* command_to_string(unsigned int command)
    {
        switch (command) {
            case HPDCACHE_MEM_READ   : return "READ";
            case HPDCACHE_MEM_WRITE  : return "STORE";
            case HPDCACHE_MEM_ATOMIC : return "ATOMIC";
            default                  : return "UNKNOWN";
        }
    }

    static const char* atomic_to_string(unsigned int atomic)
    {
        switch (atomic) {
            case HPDCACHE_MEM_ATOMIC_ADD  : return "ATOMIC_ADD";
            case HPDCACHE_MEM_ATOMIC_CLR  : return "ATOMIC_CLR";
            case HPDCACHE_MEM_ATOMIC_SET  : return "ATOMIC_SET";
            case HPDCACHE_MEM_ATOMIC_EOR  : return "ATOMIC_EOR";
            case HPDCACHE_MEM_ATOMIC_SMAX : return "ATOMIC_SMAX";
            case HPDCACHE_MEM_ATOMIC_SMIN : return "ATOMIC_SMIN";
            case HPDCACHE_MEM_ATOMIC_UMAX : return "ATOMIC_UMAX";
            case HPDCACHE_MEM_ATOMIC_UMIN : return "ATOMIC_UMIN";
            case HPDCACHE_MEM_ATOMIC_SWAP : return "ATOMIC_SWAP";
            case HPDCACHE_MEM_ATOMIC_LDEX : return "ATOMIC_LDEX";
            case HPDCACHE_MEM_ATOMIC_STEX : return "ATOMIC_STEX";
            default                       : return "UNKNOWN";
        }
    }

    virtual const std::string to_string() const = 0;
};

class hpdcache_test_transaction_mem_read_req: public hpdcache_test_transaction_mem_req
{
public:

    hpdcache_test_transaction_mem_read_req() :
        hpdcache_test_transaction_mem_req()
    {

    }

    const std::string to_string() const
    {
        std::stringstream os;

        os << "MEM_READ_REQ / @ = " << std::hex << addr << std::dec
           << " / CMD = "  << command_to_string(command)
           << " / LEN = "  << std::hex << len << std::dec
           << " / SIZE = " << std::hex << size << std::dec
           << " / ID = 0x" << std::hex << id << std::dec
           << (cacheable ? " / CACHEABLE" : " / UNCACHEABLE");
        return os.str();
    }

    friend std::ostream& operator<< (std::ostream& os,
                                     const hpdcache_test_transaction_mem_read_req& req)
    {
        os << req.to_string();
        return os;
    }
};

class hpdcache_test_transaction_mem_write_req: public hpdcache_test_transaction_mem_req
{
public:

    sc_bv<HPDCACHE_MEM_DATA_WIDTH>   data;
    sc_bv<HPDCACHE_MEM_DATA_WIDTH/8> be;
    bool                             last;

    hpdcache_test_transaction_mem_write_req() :
            data(0),
            be(0),
            last(false),
            hpdcache_test_transaction_mem_req()
    {

    }

    const std::string to_string() const
    {
        std::stringstream os;

        os << "MEM_WRITE_REQ / @ = " << std::hex << addr << std::dec
           << " / COMMAND = " << command_to_string(command);

        if (command == HPDCACHE_MEM_ATOMIC) {
            os << " / ATOMIC = "  << atomic_to_string(atomic);
        }

        os << " / LEN = "  << std::hex << len << std::dec
           << " / SIZE = " << std::hex << size << std::dec
           << " / ID = 0x" << std::hex << id << std::dec
           << " / DATA = "  << data.to_string(SC_HEX)
           << " / BE = "  << be.to_string(SC_HEX)
           << (last      ? " / LAST"      : " ")
           << (cacheable ? " / CACHEABLE" : " / UNCACHEABLE");
        return os.str();
    }

    friend std::ostream& operator<< (std::ostream& os,
                                     const hpdcache_test_transaction_mem_write_req& req)
    {
        os << req.to_string();
        return os;
    }
};

class hpdcache_test_transaction_mem_read_resp
{
public:

    uint32_t                       error;
    uint32_t                       id;
    sc_bv<HPDCACHE_MEM_DATA_WIDTH> data;
    bool                           last;

    hpdcache_test_transaction_mem_read_resp() :
            error(0),
            id(0),
            data(0),
            last(false)
    {

    }

    const std::string to_string() const
    {
        std::stringstream os;

        os << "MEM_READ_RESP / RDATA = " << data.to_string(SC_HEX)
           << " / ID = 0x" << std::hex << id << std::dec
           << (last       ? " / LAST"  : "")
           << (error != 0 ? " / ERROR" : "");
        return os.str();
    }

    friend std::ostream& operator<< (std::ostream& os,
                                     const hpdcache_test_transaction_mem_read_resp& resp)
    {
        os << resp.to_string();
        return os;
    }
};

class hpdcache_test_transaction_mem_write_resp
{
public:

    bool     is_atomic;
    uint32_t error;
    uint32_t id;

    hpdcache_test_transaction_mem_write_resp() :
            is_atomic(false),
            error(0),
            id(0)
    {

    }

    const std::string to_string() const
    {
        std::stringstream os;

        os << "MEM_WRITE_RESP"
           << " / ID = 0x" << std::hex << id << std::dec
           << (error != 0 ? " / ERROR"  : "")
           << (is_atomic  ? " / ATOMIC" : "");
        return os.str();
    }

    friend std::ostream& operator<< (std::ostream& os,
                                     const hpdcache_test_transaction_mem_write_resp& resp)
    {
        os << resp.to_string();
        return os;
    }
};

#endif /* __HPDCACHE_TEST_TRANSACTION_H__ */
