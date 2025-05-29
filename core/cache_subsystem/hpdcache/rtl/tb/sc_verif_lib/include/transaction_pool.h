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
 *  Description: Generic class definition of the transaction pool
 */
#ifndef __TRANSACTION_POOL_H__
#define __TRANSACTION_POOL_H__

#include <cassert>
#include <iostream>
#include <sstream>
#include <list>
#include <memory>
#include <string>
#include <type_traits>
#include "transaction.h"

class Transaction_pool
{
    typedef std::list<std::shared_ptr<Transaction>> Transaction_list;

public:
    Transaction_pool(int trans_bundle_sz = 10)
        : trans_bundle_sz(trans_bundle_sz)
        , nb_trans(0), nb_allocated(0), nb_release(0)
    {
    }

    template<typename T>
    std::shared_ptr<T> acquire_transaction()
    {
        std::shared_ptr<Transaction> ret;

        static_assert(std::is_convertible<T*,Transaction*>::value,
                     "T must derive from Transaction");

        // no available transaction, create some some new ones
        if (pool.empty()) {
            for (int i = 0; i < trans_bundle_sz; i++) {
                std::shared_ptr<Transaction> t = std::make_shared<T>();
                assert (t != nullptr);
                nb_allocated++;
                pool.push_back(t);
            }
        }

        // return a free transaction object
        ret = pool.front();
        pool.pop_front();

        // update the transaction ID
        ret->set_id(nb_trans++);

        return std::dynamic_pointer_cast<T>(ret);
    }

    template<typename T>
    void release_transaction(std::shared_ptr<T> &t)
    {
        static_assert(std::is_convertible<T*,Transaction*>::value,
                     "T must derive from Transaction");

        nb_release++;
        pool.push_back(std::dynamic_pointer_cast<Transaction>(t));
    }

    ~Transaction_pool() {
        std::stringstream ss;

        pool.clear();

        ss << "TRANSACTION POOL"                                   << std::endl
           << "Number of allocated transactions: " << nb_allocated << std::endl
           << "Number of acquired transactions : " << nb_trans     << std::endl
           << "Number of released transactions : " << nb_release   << std::endl;

        Logger::debug(ss.str());
    }

private:
    Transaction_list pool;
    int              trans_bundle_sz;
    uint64_t         nb_trans;
    uint64_t         nb_allocated;
    uint64_t         nb_release;
};

#endif // __TRANSACTION_POOL_H__

