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
 *  Description: Class definition of the Logger
 */
#ifndef __LOGGER_H__
#define __LOGGER_H__

#include <iostream>
#include <string>

class Logger
{
private:
    static int log_level;

public:
    enum {
        LOG_NONE    = 0,

        LOG_LOW     = 1,
        LOG_MEDIUM  = 2,
        LOG_HIGH    = 3,

        LOG_WARNING = LOG_LOW,
        LOG_INFO    = LOG_MEDIUM,
        LOG_DEBUG   = LOG_HIGH
    } log_level_e;

    Logger()          {}
    virtual ~Logger() {}

    static void set_log_level(int level)
    {
        log_level = level;
    }

    static int get_log_level()
    {
        return log_level;
    }

    static int is_warning_enabled()
    {
        return log_level >= LOG_WARNING;
    }

    static int is_info_enabled()
    {
        return log_level >= LOG_INFO;
    }

    static int is_debug_enabled()
    {
        return log_level >= LOG_DEBUG;
    }

    static void info(const std::string &msg)
    {
        if (log_level >= LOG_INFO) std::cout << msg;
    }

    static void warning(const std::string &msg)
    {
        if (log_level >= LOG_WARNING) std::cout << msg;
    }

    static void debug(const std::string &msg)
    {
        if (log_level >= LOG_DEBUG) std::cout << msg;
    }
};

int Logger::log_level = Logger::LOG_INFO;

#endif /* __LOGGER_H__ */
