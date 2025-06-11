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
 *  Description: Definition of the entry point for the HPDCACHE testbench
 */
#include <iostream>
#include <iomanip>
#include <systemc>
#include <chrono>
#include <memory>
#include <getopt.h>
#include <map>

#include <verilated.h>
#if VM_TRACE
# include <verilated_vcd_sc.h>
#endif

#include "logger.h"
#include "Vhpdcache_wrapper.h"

#include "hpdcache_test_defs.h"
#include "hpdcache_test_agent.h"
#include "hpdcache_test_scoreboard.h"
#include "hpdcache_test_mem_resp_model.h"
#include "hpdcache_test_sequence.h"
#include "sequence_lib/hpdcache_test_random_seq.h"
#include "sequence_lib/hpdcache_test_read_seq.h"
#include "sequence_lib/hpdcache_test_write_seq.h"
#include "sequence_lib/hpdcache_test_single_addr_seq.h"

class hpdcache_test
{
public:
    uint64_t max_cycles;
    uint64_t max_trans;
    bool trace_on;
    std::string trace_name;

private:
    std::string covname;
    std::shared_ptr<VerilatedVcdSc> tf;
    std::shared_ptr<hpdcache_test_sequence> seq;

public:
    hpdcache_test() :
        max_cycles(1ULL << 30),
        max_trans(100),
        covname(""),
        tf(nullptr),
        seq(nullptr)
    {
        top = std::make_shared<Vhpdcache_wrapper> ("i_top");
        hpdcache_test_agent_i = std::make_shared<hpdcache_test_agent> ("i_agent");
        hpdcache_test_mem_resp_model_i = std::make_shared<hpdcache_test_mem_resp_model> ("i_mem");
        hpdcache_test_scoreboard_i = std::make_shared<hpdcache_test_scoreboard> ("i_scoreboard");
    }

    void build()
    {
        std::cout << "Building the testbench..." << std::endl;

        top->clk_i (clk_i);
        top->rst_ni (rst_ni);
        top->wbuf_flush_i (wbuf_flush);
        top->core_req_valid_i (core_req_valid);
        top->core_req_ready_o (core_req_ready);
        top->core_req_i (core_req);
        top->core_req_abort_i (core_req_abort);
        top->core_req_tag_i (core_req_tag);
        top->core_req_pma_i (core_req_pma);
        top->core_rsp_valid_o (core_rsp_valid);
        top->core_rsp_o (core_rsp);
        top->mem_req_read_ready_i (mem_req_read_ready);
        top->mem_req_read_valid_o (mem_req_read_valid);
        top->mem_req_read_addr_o (mem_req_read_addr);
        top->mem_req_read_len_o (mem_req_read_len);
        top->mem_req_read_size_o (mem_req_read_size);
        top->mem_req_read_id_o (mem_req_read_id);
        top->mem_req_read_command_o (mem_req_read_command);
        top->mem_req_read_atomic_o (mem_req_read_atomic);
        top->mem_req_read_cacheable_o (mem_req_read_cacheable);
        top->mem_resp_read_ready_o (mem_resp_read_ready);
        top->mem_resp_read_valid_i (mem_resp_read_valid);
        top->mem_resp_read_error_i (mem_resp_read_error);
        top->mem_resp_read_id_i (mem_resp_read_id);
        top->mem_resp_read_data_i (mem_resp_read_data);
        top->mem_resp_read_last_i (mem_resp_read_last);
        top->mem_req_write_ready_i (mem_req_write_ready);
        top->mem_req_write_valid_o (mem_req_write_valid);
        top->mem_req_write_addr_o (mem_req_write_addr);
        top->mem_req_write_len_o (mem_req_write_len);
        top->mem_req_write_size_o (mem_req_write_size);
        top->mem_req_write_id_o (mem_req_write_id);
        top->mem_req_write_command_o (mem_req_write_command);
        top->mem_req_write_atomic_o (mem_req_write_atomic);
        top->mem_req_write_cacheable_o (mem_req_write_cacheable);
        top->mem_req_write_data_ready_i (mem_req_write_data_ready);
        top->mem_req_write_data_valid_o (mem_req_write_data_valid);
        top->mem_req_write_data_o (mem_req_write_data);
        top->mem_req_write_be_o (mem_req_write_be);
        top->mem_req_write_last_o (mem_req_write_last);
        top->mem_resp_write_ready_o (mem_resp_write_ready);
        top->mem_resp_write_valid_i (mem_resp_write_valid);
        top->mem_resp_write_is_atomic_i (mem_resp_write_is_atomic);
        top->mem_resp_write_error_i (mem_resp_write_error);
        top->mem_resp_write_id_i (mem_resp_write_id);
        top->evt_cache_write_miss_o (evt_cache_write_miss);
        top->evt_cache_read_miss_o (evt_cache_read_miss);
        top->evt_uncached_req_o (evt_uncached_req);
        top->evt_cmo_req_o (evt_cmo_req);
        top->evt_write_req_o (evt_write_req);
        top->evt_read_req_o (evt_read_req);
        top->evt_prefetch_req_o (evt_prefetch_req);
        top->evt_req_on_hold_o (evt_req_on_hold);
        top->evt_rtab_rollback_o (evt_rtab_rollback);
        top->evt_stall_refill_o (evt_stall_refill);
        top->evt_stall_o (evt_stall);
        top->wbuf_empty_o (wbuf_empty);
        top->cfg_enable_i (cfg_enable);
        top->cfg_wbuf_threshold_i (cfg_wbuf_threshold);
        top->cfg_wbuf_reset_timecnt_on_write_i (cfg_wbuf_reset_timecnt_on_write);
        top->cfg_wbuf_sequential_waw_i (cfg_wbuf_sequential_waw);
        top->cfg_wbuf_inhibit_write_coalescing_i (cfg_wbuf_inhibit_write_coalescing);
        top->cfg_prefetch_updt_plru_i (cfg_prefetch_updt_plru);
        top->cfg_error_on_cacheable_amo_i (cfg_error_on_cacheable_amo);
        top->cfg_rtab_single_entry_i (cfg_rtab_single_entry);
        top->cfg_default_wb_i (cfg_default_wb);

        hpdcache_test_agent_i->clk_i (clk_i);
        hpdcache_test_agent_i->rst_ni (rst_ni);
        hpdcache_test_agent_i->core_req_valid_o (core_req_valid);
        hpdcache_test_agent_i->core_req_ready_i (core_req_ready);
        hpdcache_test_agent_i->core_req_o (core_req);
        hpdcache_test_agent_i->core_req_tag_o (core_req_tag);
        hpdcache_test_agent_i->core_req_pma_o (core_req_pma);
        hpdcache_test_agent_i->core_req_abort_o (core_req_abort);
        hpdcache_test_agent_i->core_rsp_valid_i (core_rsp_valid);
        hpdcache_test_agent_i->core_rsp_i (core_rsp);
        hpdcache_test_agent_i->sb_core_req_o (sb_core_req);
        hpdcache_test_agent_i->sb_core_resp_o (sb_core_resp);

        hpdcache_test_mem_resp_model_i->clk_i (clk_i);
        hpdcache_test_mem_resp_model_i->rst_ni (rst_ni);
        hpdcache_test_mem_resp_model_i->mem_req_read_ready_o (mem_req_read_ready);
        hpdcache_test_mem_resp_model_i->mem_req_read_valid_i (mem_req_read_valid);
        hpdcache_test_mem_resp_model_i->mem_req_read_addr_i (mem_req_read_addr);
        hpdcache_test_mem_resp_model_i->mem_req_read_len_i (mem_req_read_len);
        hpdcache_test_mem_resp_model_i->mem_req_read_size_i (mem_req_read_size);
        hpdcache_test_mem_resp_model_i->mem_req_read_id_i (mem_req_read_id);
        hpdcache_test_mem_resp_model_i->mem_req_read_command_i (mem_req_read_command);
        hpdcache_test_mem_resp_model_i->mem_req_read_atomic_i (mem_req_read_atomic);
        hpdcache_test_mem_resp_model_i->mem_req_read_cacheable_i (mem_req_read_cacheable);
        hpdcache_test_mem_resp_model_i->mem_resp_read_ready_i (mem_resp_read_ready);
        hpdcache_test_mem_resp_model_i->mem_resp_read_valid_o (mem_resp_read_valid);
        hpdcache_test_mem_resp_model_i->mem_resp_read_error_o (mem_resp_read_error);
        hpdcache_test_mem_resp_model_i->mem_resp_read_id_o (mem_resp_read_id);
        hpdcache_test_mem_resp_model_i->mem_resp_read_data_o (mem_resp_read_data);
        hpdcache_test_mem_resp_model_i->mem_resp_read_last_o (mem_resp_read_last);
        hpdcache_test_mem_resp_model_i->mem_req_write_ready_o (mem_req_write_ready);
        hpdcache_test_mem_resp_model_i->mem_req_write_valid_i (mem_req_write_valid);
        hpdcache_test_mem_resp_model_i->mem_req_write_addr_i (mem_req_write_addr);
        hpdcache_test_mem_resp_model_i->mem_req_write_len_i (mem_req_write_len);
        hpdcache_test_mem_resp_model_i->mem_req_write_size_i (mem_req_write_size);
        hpdcache_test_mem_resp_model_i->mem_req_write_id_i (mem_req_write_id);
        hpdcache_test_mem_resp_model_i->mem_req_write_command_i (mem_req_write_command);
        hpdcache_test_mem_resp_model_i->mem_req_write_atomic_i (mem_req_write_atomic);
        hpdcache_test_mem_resp_model_i->mem_req_write_cacheable_i (mem_req_write_cacheable);
        hpdcache_test_mem_resp_model_i->mem_req_write_data_ready_o (mem_req_write_data_ready);
        hpdcache_test_mem_resp_model_i->mem_req_write_data_valid_i (mem_req_write_data_valid);
        hpdcache_test_mem_resp_model_i->mem_req_write_data_i (mem_req_write_data);
        hpdcache_test_mem_resp_model_i->mem_req_write_be_i (mem_req_write_be);
        hpdcache_test_mem_resp_model_i->mem_req_write_last_i (mem_req_write_last);
        hpdcache_test_mem_resp_model_i->mem_resp_write_ready_i (mem_resp_write_ready);
        hpdcache_test_mem_resp_model_i->mem_resp_write_valid_o (mem_resp_write_valid);
        hpdcache_test_mem_resp_model_i->mem_resp_write_is_atomic_o (mem_resp_write_is_atomic);
        hpdcache_test_mem_resp_model_i->mem_resp_write_error_o (mem_resp_write_error);
        hpdcache_test_mem_resp_model_i->mem_resp_write_id_o (mem_resp_write_id);
        hpdcache_test_mem_resp_model_i->sb_mem_read_req_o (sb_mem_read_req);
        hpdcache_test_mem_resp_model_i->sb_mem_read_resp_o (sb_mem_read_resp);
        hpdcache_test_mem_resp_model_i->sb_mem_write_req_o (sb_mem_write_req);
        hpdcache_test_mem_resp_model_i->sb_mem_write_resp_o (sb_mem_write_resp);

        hpdcache_test_scoreboard_i->clk_i (clk_i);
        hpdcache_test_scoreboard_i->core_req_i (sb_core_req);
        hpdcache_test_scoreboard_i->core_resp_i (sb_core_resp);
        hpdcache_test_scoreboard_i->mem_read_req_i (sb_mem_read_req);
        hpdcache_test_scoreboard_i->mem_read_resp_i (sb_mem_read_resp);
        hpdcache_test_scoreboard_i->mem_write_req_i (sb_mem_write_req);
        hpdcache_test_scoreboard_i->mem_write_resp_i (sb_mem_write_resp);
        hpdcache_test_scoreboard_i->evt_cache_write_miss_i (evt_cache_write_miss);
        hpdcache_test_scoreboard_i->evt_cache_read_miss_i (evt_cache_read_miss);
        hpdcache_test_scoreboard_i->evt_uncached_req_i (evt_uncached_req);
        hpdcache_test_scoreboard_i->evt_cmo_req_i (evt_cmo_req);
        hpdcache_test_scoreboard_i->evt_write_req_i (evt_write_req);
        hpdcache_test_scoreboard_i->evt_read_req_i (evt_read_req);
        hpdcache_test_scoreboard_i->evt_prefetch_req_i (evt_prefetch_req);
        hpdcache_test_scoreboard_i->evt_req_on_hold_i (evt_req_on_hold);
        hpdcache_test_scoreboard_i->evt_rtab_rollback_i (evt_rtab_rollback);
        hpdcache_test_scoreboard_i->evt_stall_refill_i (evt_stall_refill);
        hpdcache_test_scoreboard_i->evt_stall_i (evt_stall);

        seq->set_max_transactions(this->max_trans);
        seq->set_mem_resp_model(hpdcache_test_mem_resp_model_i);
        hpdcache_test_agent_i->add_sequence(seq);
        hpdcache_test_scoreboard_i->set_sequence(seq);
        hpdcache_test_scoreboard_i->set_mem_resp_model(hpdcache_test_mem_resp_model_i);
    }

    void simulate()
    {
        std::chrono::time_point<std::chrono::system_clock> start, end;
        uint64_t cycles;

        std::cout << "Starting the simulation..." << std::endl;
        std::cout << *seq << std::endl;

        cycles = 0;
        start = std::chrono::system_clock::now();
        sc_start(sc_core::SC_ZERO_TIME);

        if (trace_on) this->trace(trace_name);

        wbuf_flush.write (false);
        cfg_enable.write (true);
        cfg_wbuf_threshold.write (1);
        cfg_wbuf_reset_timecnt_on_write.write (true);
        cfg_wbuf_sequential_waw.write (false);
        cfg_wbuf_inhibit_write_coalescing.write (false);
        cfg_prefetch_updt_plru.write (false);
        cfg_error_on_cacheable_amo.write (false);
        cfg_rtab_single_entry.write (false);
        cfg_default_wb.write (false);

        Verilated::assertOn(false);
        rst_ni = 1;
        for (cycles = 0; cycles < 5; ++cycles) {
            clk_i = 0;
            sc_start(500, sc_core::SC_PS);
            clk_i = 1;
            sc_start(500, sc_core::SC_PS);
        }
        Verilated::assertOn(true);
        rst_ni = 0;
        for (cycles = 0; cycles < 5; ++cycles) {
            clk_i = 0;
            sc_start(500, sc_core::SC_PS);
            clk_i = 1;
            sc_start(500, sc_core::SC_PS);
        }
        rst_ni = 1;
        for (; cycles < max_cycles; ++cycles) {
            clk_i = 0;
            sc_start(500, sc_core::SC_PS);
            if (Verilated::gotFinish()) break;
            clk_i = 1;
            sc_start(500, sc_core::SC_PS);
            if (Verilated::gotFinish()) break;
        }
        end = std::chrono::system_clock::now();
        std::cout << "Finishing the simulation..." << std::endl;

        int ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        std::cout << "Simulation wall clock time (sec): "
                  << std::fixed << std::setprecision(2) << (double)ms/1000
                  << std::endl;
        std::cout << "Simulation real frequency       : "
                  << std::fixed << std::setprecision(2) << (double)cycles/ms << " KHz"
                  << std::endl;
    }

    void set_sequence(std::string seq_name)
    {
        if (seq != nullptr) {
            std::cout << "error: only one sequence supported" << std::endl;
            exit(EXIT_FAILURE);
        }

        if (seq_name == "random") {
            seq = std::make_shared<hpdcache_test_random_seq>("random");
        } else if (seq_name == "read") {
            seq = std::make_shared<hpdcache_test_read_seq>("read");
        } else if (seq_name == "write") {
            seq = std::make_shared<hpdcache_test_write_seq>("write");
        } else if (seq_name == "single_addr") {
            seq = std::make_shared<hpdcache_test_single_addr_seq>("single_addr");
        } else {
            std::cout << "error: sequence " << seq_name << " not found" << std::endl;
            exit(EXIT_FAILURE);
        }
    }

    void trace(const std::string tracename)
    {
#if VM_TRACE
        std::cout << "Dumping waves into " << tracename << std::endl;
        tf = std::make_shared<VerilatedVcdSc>();
        Verilated::traceEverOn(true);
        top->trace(tf.get(), 99);  // Trace 99 levels of hierarchy
        tf->open(tracename.c_str());
#endif
    }

    void coverage(const std::string filename)
    {
        this->covname = filename;
    }

    ~hpdcache_test()
    {
#if VM_TRACE
        if (tf != nullptr) {
            tf->close();
        }
#endif
#if VM_COVERAGE
        if (covname != "") {
            VerilatedCov::write(covname.c_str());
        }
#endif
    }

private:


    std::shared_ptr<Vhpdcache_wrapper> top;
    std::shared_ptr<hpdcache_test_agent> hpdcache_test_agent_i;
    std::shared_ptr<hpdcache_test_mem_resp_model> hpdcache_test_mem_resp_model_i;
    std::shared_ptr<hpdcache_test_scoreboard> hpdcache_test_scoreboard_i;

    sc_core::sc_signal <bool> clk_i;
    sc_core::sc_signal <bool> rst_ni;
    sc_core::sc_signal <bool> wbuf_flush;
    sc_core::sc_signal <bool> core_req_valid;
    sc_core::sc_signal <bool> core_req_ready;
    sc_core::sc_signal <sc_bv<HPDCACHE_CORE_REQ_WIDTH> > core_req;
    sc_core::sc_signal <bool> core_req_abort;
    sc_core::sc_signal <uint64_t> core_req_tag;
    sc_core::sc_signal <uint32_t> core_req_pma;
    sc_core::sc_signal <bool> core_rsp_valid;
    sc_core::sc_signal <sc_bv<HPDCACHE_CORE_RSP_WIDTH> > core_rsp;

    sc_core::sc_signal <bool> mem_req_read_ready;
    sc_core::sc_signal <bool> mem_req_read_valid;
    sc_core::sc_signal <uint64_t> mem_req_read_addr;
    sc_core::sc_signal <uint32_t> mem_req_read_len;
    sc_core::sc_signal <uint32_t> mem_req_read_size;
    sc_core::sc_signal <uint32_t> mem_req_read_id;
    sc_core::sc_signal <uint32_t> mem_req_read_command;
    sc_core::sc_signal <uint32_t> mem_req_read_atomic;
    sc_core::sc_signal <bool> mem_req_read_cacheable;
    sc_core::sc_signal <bool> mem_resp_read_ready;
    sc_core::sc_signal <bool> mem_resp_read_valid;
    sc_core::sc_signal <uint32_t> mem_resp_read_error;
    sc_core::sc_signal <uint32_t> mem_resp_read_id;
    sc_core::sc_signal <sc_bv<HPDCACHE_MEM_DATA_WIDTH> > mem_resp_read_data;
    sc_core::sc_signal <bool> mem_resp_read_last;
    sc_core::sc_signal <bool> mem_req_write_ready;
    sc_core::sc_signal <bool> mem_req_write_valid;
    sc_core::sc_signal <uint64_t> mem_req_write_addr;
    sc_core::sc_signal <uint32_t> mem_req_write_len;
    sc_core::sc_signal <uint32_t> mem_req_write_size;
    sc_core::sc_signal <uint32_t> mem_req_write_id;
    sc_core::sc_signal <uint32_t> mem_req_write_command;
    sc_core::sc_signal <uint32_t> mem_req_write_atomic;
    sc_core::sc_signal <bool> mem_req_write_cacheable;
    sc_core::sc_signal <bool> mem_req_write_data_ready;
    sc_core::sc_signal <bool> mem_req_write_data_valid;
    sc_core::sc_signal <sc_bv<HPDCACHE_MEM_DATA_WIDTH> > mem_req_write_data;
    sc_core::sc_signal <uint64_t> mem_req_write_be;
    sc_core::sc_signal <bool> mem_req_write_last;
    sc_core::sc_signal <bool> mem_resp_write_ready;
    sc_core::sc_signal <bool> mem_resp_write_valid;
    sc_core::sc_signal <bool> mem_resp_write_is_atomic;
    sc_core::sc_signal <uint32_t> mem_resp_write_error;
    sc_core::sc_signal <uint32_t> mem_resp_write_id;

    sc_core::sc_fifo<hpdcache_test_transaction_req> sb_core_req;
    sc_core::sc_fifo<hpdcache_test_transaction_resp> sb_core_resp;
    sc_core::sc_fifo<hpdcache_test_transaction_mem_read_req> sb_mem_read_req;
    sc_core::sc_fifo<hpdcache_test_transaction_mem_read_resp> sb_mem_read_resp;
    sc_core::sc_fifo<hpdcache_test_transaction_mem_write_req> sb_mem_write_req;
    sc_core::sc_fifo<hpdcache_test_transaction_mem_write_resp> sb_mem_write_resp;

    sc_core::sc_signal <bool> evt_cache_write_miss;
    sc_core::sc_signal <bool> evt_cache_read_miss;
    sc_core::sc_signal <bool> evt_uncached_req;
    sc_core::sc_signal <bool> evt_cmo_req;
    sc_core::sc_signal <bool> evt_write_req;
    sc_core::sc_signal <bool> evt_read_req;
    sc_core::sc_signal <bool> evt_prefetch_req;
    sc_core::sc_signal <bool> evt_req_on_hold;
    sc_core::sc_signal <bool> evt_rtab_rollback;
    sc_core::sc_signal <bool> evt_stall_refill;
    sc_core::sc_signal <bool> evt_stall;

    sc_core::sc_signal <bool> wbuf_empty;

    sc_core::sc_signal <bool> cfg_enable;
    sc_core::sc_signal <uint32_t> cfg_wbuf_threshold;
    sc_core::sc_signal <bool> cfg_wbuf_reset_timecnt_on_write;
    sc_core::sc_signal <bool> cfg_wbuf_sequential_waw;
    sc_core::sc_signal <bool> cfg_wbuf_inhibit_write_coalescing;
    sc_core::sc_signal <bool> cfg_prefetch_updt_plru;
    sc_core::sc_signal <bool> cfg_error_on_cacheable_amo;
    sc_core::sc_signal <bool> cfg_rtab_single_entry;
    sc_core::sc_signal <bool> cfg_default_wb;
};

void usage(const char* argv)
{

}

int sc_main(int argc, char** argv)
{
    hpdcache_test test;
    bool write_coverage_data;

    Verilated::commandArgs(argc, argv);
    for (;;) {
        int c;
        int option_index;
        static struct option long_options[] = {
            {"help",        no_argument,       0, 'h' },
            {"max-cycles",  required_argument, 0, 'm' },
            {"seed",        required_argument, 0, 'r' },
            {"log-level",   required_argument, 0, 'l' },
            {"trace",       required_argument, 0, 't' },
            {"coverage",    required_argument, 0, 'c' },
            {"sequence",    required_argument, 0, 's' },
            {0,             0                , 0,  0  }
        };

        option_index = 0;
        c = getopt_long(argc, argv, "hm:n:r:c:l:t:s:", long_options, &option_index);
        if (c == -1) break;

        switch (c) {
            case '?': case 'h':
                usage(argv[0]);
                return 0;
            case 'm':
                test.max_cycles = atoll(optarg);
                break;
            case 'n':
                test.max_trans = atoll(optarg);
                break;
            case 'r':
            {
                unsigned long int seed = strtol(optarg, NULL, 0);
                srand(seed);
                scv_random::set_global_seed(seed);
                break;
            }
            case 't':
                test.trace_on   = true;
                test.trace_name = optarg;
                break;
            case 'c':
                test.coverage(optarg);
                break;
            case 'l': {
                const int level = atoi(optarg);
                sc_core::sc_verbosity verbosity;

                switch (level) {
                    case 0: verbosity = sc_core::SC_NONE  ; break;
                    case 1: verbosity = sc_core::SC_LOW   ; break;
                    case 2: verbosity = sc_core::SC_MEDIUM; break;
                    case 3: verbosity = sc_core::SC_HIGH  ; break;
                    case 4: verbosity = sc_core::SC_FULL  ; break;
                    case 5: verbosity = sc_core::SC_DEBUG ; break;
                    default:
                        std::cout << "error: unsupported verbosity level" << std::endl;
                        exit(EXIT_FAILURE);
                }

                std::cout << "info: setting log level to: " << level << std::endl;
                Logger::set_log_level(level);
                sc_core::sc_report_handler::set_verbosity_level(verbosity);
                break;
            }
            case 's':
                test.set_sequence(optarg);
                break;
        }
    }

    test.build();
    test.simulate();
    return 0;
}
