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
 *  Description: Generic class definition of the sequence
 */
#ifndef __SEQUENCE_H__
#define __SEQUENCE_H__

#include <systemc>
#include <memory>
#include "transaction_pool.h"

class Transaction;

class Sequence : public sc_core::sc_module
{
public:
    sc_core::sc_in<bool>                               clk_i;
    sc_core::sc_in<bool>                               rst_ni;
    sc_core::sc_fifo_out<std::shared_ptr<Transaction>> transaction_fifo_o;
    sc_core::sc_fifo_in<uint64_t>                      transaction_ret_i;

    Sequence(sc_core::sc_module_name nm)
        : sc_module(nm)
        , clk_i("clk_i")
        , rst_ni("rst_ni")
        , transaction_fifo_o("transaction_fifo_o")
        , transaction_ret_i("transaction_ret_i")
    {
    }

    virtual ~Sequence() {};

    template<typename T>
    std::shared_ptr<T> acquire_transaction()
    {
        std::shared_ptr<T> ret = transaction_pool.acquire_transaction<T>();
        *ret = T(); // initialize
        return ret;
    }

    template<typename T>
    std::shared_ptr<T> acquire_transaction(const T& init)
    {
        std::shared_ptr<T> ret = transaction_pool.acquire_transaction<T>();
        uint64_t id = ret->get_id();
        *ret = init; // copy
        ret->set_id(id); // restore new id
        return ret;
    }

    template<typename T>
    void release_transaction(std::shared_ptr<T> t)
    {
        transaction_pool.release_transaction<T>(t);
    }

protected:
    Transaction_pool transaction_pool;
};

#endif // __SEQUENCE_H__

