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
 *  Description: Class definition of the Transaction
 */
#ifndef __TRANSACTION_H__
#define __TRANSACTION_H__

#include <cstdint>

class Transaction
{
public:
    Transaction() : __id(0) {}
    virtual ~Transaction() {}
    virtual const std::string to_string() const = 0;

    void set_id(uint64_t id)
    {
        __id = id;
    };

    uint64_t get_id() {
        return __id;
    };

protected:
    uint64_t __id; // transaction ID
};

#endif /* __TRANSACTION_H__ */

