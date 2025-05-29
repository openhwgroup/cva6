/**
 * Copyright 2023,2024 CEA*
 * *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 * Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 * may not use this file except in compliance with the License, or, at your
 * option, the Apache License version 2.0. You may obtain a copy of the
 * License at
 *
 * https://solderpad.org/licenses/SHL-2.1/
 *
 * Unless required by applicable law or agreed to in writing, any work
 * distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
/**
 *  Author     : Cesar Fuguet
 *  Date       : September, 2024
 *  Description: Class definition of the hpdcache_test_agent
 */
#ifndef __HPDCACHE_TEST_AGENT_H__
#define __HPDCACHE_TEST_AGENT_H__

#include <iostream>
#include <sstream>
#include <list>
#include <systemc>
#include <verilated.h>

#include "agent.h"
#include "sequence.h"
#include "hpdcache_test_driver.h"
#include "hpdcache_test_defs.h"
#include "logger.h"

class hpdcache_test_agent : public Agent
{
public:
    sc_out <bool>                                core_req_valid_o;
    sc_in  <bool>                                core_req_ready_i;
    sc_out <sc_bv<HPDCACHE_CORE_REQ_WIDTH> >     core_req_o;
    sc_out <uint64_t>                            core_req_tag_o;
    sc_out <uint32_t>                            core_req_pma_o;
    sc_out <bool>                                core_req_abort_o;

    sc_in  <bool>                                core_rsp_valid_i;
    sc_in  <sc_bv<HPDCACHE_CORE_RSP_WIDTH> >     core_rsp_i;

    sc_fifo_out<hpdcache_test_transaction_req>   sb_core_req_o;
    sc_fifo_out<hpdcache_test_transaction_resp>  sb_core_resp_o;

    hpdcache_test_agent(sc_core::sc_module_name nm)
      : Agent(nm)
      , core_req_valid_o("core_req_valid_o")
      , core_req_ready_i("core_req_ready_i")
      , core_req_o("core_req_o")
      , core_req_tag_o("core_req_tag_o")
      , core_req_pma_o("core_req_pma_o")
      , core_req_abort_o("core_req_abort_o")
      , core_rsp_valid_i("core_rsp_valid_i")
      , core_rsp_i("core_rsp_i")
      , sb_core_req_o("sb_core_req_o")
      , sb_core_resp_o("sb_core_resp_o")
    {
        std::string driver_name;

        driver_name = std::string(nm) + "_driver";

        driver = std::make_shared<hpdcache_test_driver>(driver_name.c_str());
        driver->clk_i              (Agent::clk_i);
        driver->rst_ni             (Agent::rst_ni);

        driver->core_req_valid_o   (core_req_valid_o);
        driver->core_req_ready_i   (core_req_ready_i);
        driver->core_req_o         (core_req_o);
        driver->core_req_tag_o     (core_req_tag_o);
        driver->core_req_pma_o     (core_req_pma_o);
        driver->core_req_abort_o   (core_req_abort_o);

        driver->core_rsp_valid_i   (core_rsp_valid_i);
        driver->core_rsp_i         (core_rsp_i);

        driver->sb_core_req_o      (sb_core_req_o);
        driver->sb_core_resp_o     (sb_core_resp_o);

        driver->transaction_fifo_i (Agent::transaction_fifo);
        driver->transaction_ret_o  (Agent::transaction_ret);
    }

    ~hpdcache_test_agent()
    {
    }

private:
    std::shared_ptr<hpdcache_test_driver> driver;
};

#endif /* __HPDCACHE_TEST_AGENT_H__ */
