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
 *  Description: Generic class definition of the agent
 */
#ifndef __AGENT_H__
#define __AGENT_H__

#include <string>
#include <iostream>
#include <list>
#include <systemc>
#include "transaction.h"
#include "sequence.h"

class Agent : public sc_core::sc_module
{
    typedef std::list<std::shared_ptr<Sequence>> Sequence_list;
    typedef Sequence_list::const_iterator        Sequence_iterator;

public:
    sc_core::sc_in<bool> clk_i;
    sc_core::sc_in<bool> rst_ni;

    Agent(sc_core::sc_module_name nm)
        : sc_module(nm)
        , clk_i("clk_i")
        , rst_ni("rst_ni")
        , transaction_fifo("transaction_fifo")
        , transaction_ret("transaction_ret") {/*empty*/}

    virtual ~Agent() {
        slist.clear();
    }

    void add_sequence(std::shared_ptr<Sequence> seq)
    {
        seq->clk_i              (clk_i);
        seq->rst_ni             (rst_ni);
        seq->transaction_fifo_o (transaction_fifo);
        seq->transaction_ret_i  (transaction_ret);

        slist.push_back(seq);
    }

    Sequence_list get_sequence_list()
    {
        return slist;
    }

protected:
    sc_core::sc_fifo<std::shared_ptr<Transaction>> transaction_fifo;
    sc_core::sc_fifo<uint64_t>                     transaction_ret;

private:
    Sequence_list slist;
};

#endif // __AGENT_H__
