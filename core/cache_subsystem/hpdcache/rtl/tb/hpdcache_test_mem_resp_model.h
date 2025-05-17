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
#ifndef __HPDCACHE_TEST_MEM_RESP_MODEL_H__
#define __HPDCACHE_TEST_MEM_RESP_MODEL_H__

#include <systemc>
#include <map>
#include <iostream>
#include <scv.h>
#include "hpdcache_test_defs.h"
#include "hpdcache_test_mem_resp_model_base.h"
#include "mem_model.h"
#include "logger.h"

#define DEBUG_HPDCACHE_TEST_MEM_RESP_MODEL 1

class hpdcache_test_mem_resp_model : public sc_module, public hpdcache_test_mem_resp_model_base
{
public:

    sc_in<bool>                                            clk_i;
    sc_in<bool>                                            rst_ni;

    sc_out<bool>                                           mem_req_read_ready_o;
    sc_in<bool>                                            mem_req_read_valid_i;
    sc_in<uint64_t>                                        mem_req_read_addr_i;
    sc_in<uint32_t>                                        mem_req_read_len_i;
    sc_in<uint32_t>                                        mem_req_read_size_i;
    sc_in<uint32_t>                                        mem_req_read_id_i;
    sc_in<uint32_t>                                        mem_req_read_command_i;
    sc_in<uint32_t>                                        mem_req_read_atomic_i;
    sc_in<bool>                                            mem_req_read_cacheable_i;

    sc_in<bool>                                            mem_resp_read_ready_i;
    sc_out<bool>                                           mem_resp_read_valid_o;
    sc_out<uint32_t>                                       mem_resp_read_error_o;
    sc_out<uint32_t>                                       mem_resp_read_id_o;
    sc_out<sc_bv<HPDCACHE_MEM_DATA_WIDTH> >                mem_resp_read_data_o;
    sc_out<bool>                                           mem_resp_read_last_o;

    sc_out<bool>                                           mem_req_write_ready_o;
    sc_in<bool>                                            mem_req_write_valid_i;
    sc_in<uint64_t>                                        mem_req_write_addr_i;
    sc_in<uint32_t>                                        mem_req_write_len_i;
    sc_in<uint32_t>                                        mem_req_write_size_i;
    sc_in<uint32_t>                                        mem_req_write_id_i;
    sc_in<uint32_t>                                        mem_req_write_command_i;
    sc_in<uint32_t>                                        mem_req_write_atomic_i;
    sc_in<bool>                                            mem_req_write_cacheable_i;

    sc_out<bool>                                           mem_req_write_data_ready_o;
    sc_in<bool>                                            mem_req_write_data_valid_i;
    sc_in<sc_bv<HPDCACHE_MEM_DATA_WIDTH> >                 mem_req_write_data_i;
    sc_in<uint64_t>                                        mem_req_write_be_i;
    sc_in<bool>                                            mem_req_write_last_i;

    sc_in<bool>                                            mem_resp_write_ready_i;
    sc_out<bool>                                           mem_resp_write_valid_o;
    sc_out<bool>                                           mem_resp_write_is_atomic_o;
    sc_out<uint32_t>                                       mem_resp_write_error_o;
    sc_out<uint32_t>                                       mem_resp_write_id_o;

    sc_fifo_out<hpdcache_test_transaction_mem_read_req>    sb_mem_read_req_o;
    sc_fifo_out<hpdcache_test_transaction_mem_read_resp>   sb_mem_read_resp_o;
    sc_fifo_out<hpdcache_test_transaction_mem_write_req>   sb_mem_write_req_o;
    sc_fifo_out<hpdcache_test_transaction_mem_write_resp>  sb_mem_write_resp_o;

private:

#if SC_VERSION_MAJOR < 3
    SC_HAS_PROCESS(hpdcache_test_mem_resp_model);
#endif

public:

    hpdcache_test_mem_resp_model(sc_module_name nm) :
            sc_module(nm),
            hpdcache_test_mem_resp_model_base(std::string(nm))
    {
        SC_THREAD(read_process);
        sensitive << clk_i.neg();

        SC_THREAD(read_response_process);
        sensitive << clk_i.pos();

        SC_THREAD(write_address_process);
        sensitive << clk_i.neg();

        SC_THREAD(write_data_process);
        sensitive << clk_i.neg();

        SC_THREAD(write_process);
        sensitive << clk_i.pos();

        SC_THREAD(write_response_process);
        sensitive << clk_i.pos();
    }

private:

    void readOperation()
    {
        hpdcache_test_transaction_mem_read_req  req;
        hpdcache_test_transaction_mem_read_resp resp;

        //  consume the request from the request ports
        req.addr      = mem_req_read_addr_i.read();
        req.len       = mem_req_read_len_i.read();
        req.size      = mem_req_read_size_i.read();
        req.id        = mem_req_read_id_i.read();
        req.command   = mem_req_read_command_i.read();
        req.atomic    = mem_req_read_atomic_i.read();
        req.cacheable = mem_req_read_cacheable_i.read();
        sb_mem_read_req_o.write(req); // send request to scoreboard

        ra_ready_delay->next();
        for (int i = 0; i < ra_ready_delay->read(); i++) wait();

        mem_req_read_ready_o.write(true);
        wait();
        mem_req_read_ready_o.write(false);

        //  check if the address is in an error segment. If it is, send a
        //  response with the error flag asserted
        uint64_t addr     = req.addr;
        uint64_t end_addr = addr + (1ULL << req.size);
        if (within_error_region(addr, end_addr)) {
            for (int i = 0; i < (req.len + 1); i++) {
                resp.error = 1;
                resp.id = req.id;
                resp.last = (i == req.len);
                read_resp_fifo.write(resp);
            }
            return;
        }

        //  do the read operation on the memory array
        size_t words = (1 << req.size)/8;
        if (words == 0) words = 1;

        if (req.is_ldex()) {
            const uint64_t n  = 1 << req.size;
            excl_buf_m[req.id].valid     = true;
            excl_buf_m[req.id].base_addr = addr;
            excl_buf_m[req.id].end_addr  = addr + n;
        }

        for (int i = 0; i < (req.len + 1); i++) {
            for (int w = 0; w < words; w++) {
                uint64_t word_addr = (addr >> 3) + w;
                uint64_t ld_data = memory_m->readMemory(word_addr);
                uint64_t r = word_addr % MEM_NOC_DATA_WORDS;
                resp.data.range((r + 1)*64 - 1, r*64) = ld_data;

#if DEBUG_HPDCACHE_TEST_MEM_RESP_MODEL
                if (check_verbosity(sc_core::SC_DEBUG)) {
                    std::cout << sc_time_stamp().to_string()
                              << " / MEM_RESP_MODEL_DEBUG: reading memory"
                              << " / address = 0x"   << std::hex << word_addr*8 << std::dec
                              << " / load data = 0x" << std::hex << ld_data     << std::dec
                              << std::endl;
                }
#endif
            }

            //  send response
            resp.error = 0;
            resp.id = req.id;
            resp.last = (i == req.len);
            read_resp_fifo.write(resp);

            addr = ((addr >> 3) + words) << 3;
        }
    }

    void writeOperation(hpdcache_test_transaction_mem_write_req req)
    {
        hpdcache_test_transaction_mem_write_resp resp;

        unsigned int command = req.command;
        unsigned bytes       = (1ULL << req.size);
        uint64_t addr        = req.addr;
        uint64_t end_addr    = addr + bytes;
        uint64_t word_addr   = addr >> 3;
        bool     excl_ok     = false;

        unsigned int atop = req.atomic;
        bool       is_amo = ((command == hpdcache_mem_command_e::HPDCACHE_MEM_ATOMIC) &&
                             (atop    != hpdcache_mem_atomic_e::HPDCACHE_MEM_ATOMIC_STEX));

        //  check if the address is in an error segment. If it is, send a
        //  response with the error flag asserted
        if (within_error_region(addr, end_addr)) {
            if (is_amo) {
                hpdcache_test_transaction_mem_read_resp read_resp;
                read_resp.data = 0;
                read_resp.error = 0;
                read_resp.id = req.id;
                read_resp.last = true;
                read_resp_fifo.write(read_resp);
            }

            resp.is_atomic = 0;
            resp.error = 1;
            resp.id = req.id;
            write_resp_fifo.write(resp);
            return;
        }

        if (req.is_stex()) {
            excl_reservation_buf_t& e = excl_buf_m[req.id];
            if (e.valid) {
                e.valid = false;
                excl_ok = within_region(addr, end_addr, e.base_addr, e.end_addr);
            }
        }

        //  compute the AMO result
        uint64_t word = word_addr % MEM_NOC_DATA_WORDS;
        uint64_t ld_data;
        uint64_t st_data;
        uint64_t amo_result;

        if (is_amo) {
            unsigned offset = (addr % 8) * 8;

            ld_data = memory_m->readMemory(word_addr);
            st_data = req.data.range((word + 1)*64 - 1, word*64).to_uint64();
            if (bytes == 4) {
                ld_data = static_cast<uint32_t>(ld_data >> offset);
                st_data = static_cast<uint32_t>(st_data >> offset);
            }
            amo_result = compute_amo(static_cast<hpdcache_mem_atomic_e>(atop), ld_data, st_data, bytes);
            if (offset) {
                ld_data    <<= offset;
                st_data    <<= offset;
                amo_result <<= offset;
            }

#if DEBUG_HPDCACHE_TEST_MEM_RESP_MODEL
            if (check_verbosity(sc_core::SC_DEBUG)) {
                std::cout << sc_time_stamp().to_string()
                          << " / MEM_RESP_MODEL_DEBUG: computing amo word"
                          << " / load data = 0x"  << std::hex << ld_data    << std::dec
                          << " / store data = 0x" << std::hex << st_data    << std::dec
                          << " / amo result = 0x" << std::hex << amo_result << std::dec
                          << std::endl;
            }
#endif
        }

        //  compute the number of words to write
        if (!req.is_stex() || excl_ok) {
            size_t words = bytes/8;
            if (words == 0) words = 1;

            //  do the write operation on the memory array
            for (int w = 0; w < words; w++) {
                unsigned int i = word + w;
                uint8_t be = req.be.range((i + 1)*8 - 1, i*8).to_uint();

                //  skip the write operation if the byte enable is all 0
                if (be == 0) continue;

                st_data = is_amo ? amo_result : req.data.range((i + 1)*64 - 1, i*64).to_uint64();
                memory_m->writeMemory(word_addr + w, st_data, mem_model::beToMask(be));

#if DEBUG_HPDCACHE_TEST_MEM_RESP_MODEL
                if (check_verbosity(sc_core::SC_DEBUG)) {
                    std::cout << sc_time_stamp().to_string()
                              << " / MEM_RESP_MODEL_DEBUG: writing memory"
                              << " / address = 0x"    << std::hex << ((word_addr + w)*8) << std::dec
                              << " / store data = 0x" << std::hex << st_data             << std::dec
                              << " / store be = 0x"   << std::hex << (uint32_t)be        << std::dec
                              << std::endl;
                }
#endif
            }

            //  send the old data for AMO on the read response channel
            if (is_amo) {
                hpdcache_test_transaction_mem_read_resp read_resp;
                read_resp.data = 0;
                read_resp.data.range((word + 1)*64 - 1, word*64) = ld_data;
                read_resp.error = 0;
                read_resp.id = req.id;
                read_resp.last = true;
                read_resp_fifo.write(read_resp);
            }
        }

        //  send the write acknowledge on the write response channel
        resp.is_atomic = req.is_stex() && excl_ok;
        resp.error = 0;
        resp.id = req.id;
        write_resp_fifo.write(resp);
    }

    void read_response_process()
    {
        hpdcache_test_transaction_mem_read_resp read_resp;

        mem_resp_read_valid_o.write(false);
        for (;;) {
            read_resp_fifo.read(read_resp);
            rd_valid_delay->next();
            for (int i = 0; i < rd_valid_delay->read(); i++) wait();
            sb_mem_read_resp_o.write(read_resp); // send response to scoreboard
            mem_resp_read_valid_o.write(true);
            mem_resp_read_error_o.write(read_resp.error);
            mem_resp_read_id_o.write(read_resp.id);
            mem_resp_read_data_o.write(read_resp.data);
            mem_resp_read_last_o.write(read_resp.last);
            do wait(); while (!mem_resp_read_ready_i.read());
            mem_resp_read_valid_o.write(false);
        }
    }

    void write_response_process()
    {
        hpdcache_test_transaction_mem_write_resp resp;

        mem_resp_write_valid_o.write(false);
        for (;;) {
            write_resp_fifo.read(resp);
            wb_valid_delay->next();
            for (int i = 0; i < wb_valid_delay->read(); i++) wait();
            sb_mem_write_resp_o.write(resp); // send response to scoreboard
            mem_resp_write_valid_o.write(true);
            mem_resp_write_is_atomic_o.write(resp.is_atomic);
            mem_resp_write_error_o.write(resp.error);
            mem_resp_write_id_o.write(resp.id);
            do wait(); while (!mem_resp_write_ready_i.read());
            mem_resp_write_valid_o.write(false);
        }
    }

    void read_process()
    {
        mem_req_read_ready_o.write(false);
        for (;;) {
            if (mem_req_read_valid_i.read()) {
                readOperation();
            } else {
                wait();
            }
        }
    }

    void write_address_process()
    {
        //
        //  This process consumes beats on the Write Channel
        //
        mem_write_req_flit_t r;
        for (;;) {
            mem_req_write_ready_o.write(false);

            //  Wait for a write request
            while (!mem_req_write_valid_i.read()) wait();

            //  Wait for a random delay before setting the ready signal
            wa_ready_delay->next();
            for (int i = 0; i < wa_ready_delay->read(); ++i) wait();

            //  Set the ready signal
            mem_req_write_ready_o.write(true);

            //  Forward the request to the write process
            r.addr = mem_req_write_addr_i.read();
            r.len = mem_req_write_len_i.read();
            r.size = mem_req_write_size_i.read();
            r.id = mem_req_write_id_i.read();
            r.command = mem_req_write_command_i.read();
            r.atomic = mem_req_write_atomic_i.read();
            r.cacheable = mem_req_write_cacheable_i.read();
            write_req_fifo.write(r);

            wait();
        }
    }

    void write_data_process()
    {
        //
        //  This process consumes beats on the Write Data Channel
        //
        mem_write_req_data_flit_t r;
        for (;;) {
            mem_req_write_data_ready_o.write(false);

            //  Wait for a data beat
            while (!mem_req_write_data_valid_i.read()) wait();

            //  Wait for a random delay before setting the ready signal
            wd_ready_delay->next();
            for (int i = 0; i < wd_ready_delay->read(); ++i) wait();

            //  Set the ready signal
            mem_req_write_data_ready_o.write(true);

            r.data = mem_req_write_data_i.read();
            r.be = mem_req_write_be_i.read();
            r.last = mem_req_write_last_i.read();
            write_req_data_fifo.write(r);

            wait();
        }
    }

    void write_process()
    {
        mem_write_req_flit_t req_meta;
        mem_write_req_data_flit_t req_data;
        hpdcache_test_transaction_mem_write_req req;

        for (;;) {
            write_req_fifo.read(req_meta);
            write_req_data_fifo.read(req_data);
            wait();

            if (req_meta.len != 0) {
                std::cout << sc_time_stamp().to_string()
                          << " / Error: this model currently supports single"
                          << " flit transactions" << std::endl;
            }

            req.addr = req_meta.addr;
            req.len = req_meta.len;
            req.size = req_meta.size;
            req.id = req_meta.id;
            req.command = req_meta.command;
            req.atomic = req_meta.atomic;
            req.cacheable = req_meta.cacheable;
            req.data = req_data.data;
            req.be = req_data.be;
            req.last = req_data.last;

            //  send request to scoreboard
            sb_mem_write_req_o.write(req);

            //  make the write operation
            writeOperation(req);
        }
    }
};

#endif /* __HPDCACHE_TEST_MEM_RESP_MODEL_H__ */
