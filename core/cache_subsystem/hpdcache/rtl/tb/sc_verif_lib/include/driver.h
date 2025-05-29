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
 *  Description: Generic class definition of the driver
 */
#ifndef __DRIVER_H__
#define __DRIVER_H__

#include <string>
#include <systemc>
#include "driver.h"

class Transaction;

class Driver : public sc_core::sc_module
{
public:
    sc_core::sc_in       < bool >                         clk_i;
    sc_core::sc_in       < bool >                         rst_ni;
    sc_core::sc_fifo_in  < std::shared_ptr<Transaction> > transaction_fifo_i;
    sc_core::sc_fifo_out < uint64_t >                     transaction_ret_o;

    Driver(sc_core::sc_module_name nm)
        : sc_module(nm)
        , clk_i("clk_i")
        , rst_ni("rst_ni")
        , transaction_fifo_i("transaction_fifo_i")
        , transaction_ret_o("transaction_ret_o")
    {
    };

    virtual ~Driver() {}
};

#endif // __DRIVER_H__

