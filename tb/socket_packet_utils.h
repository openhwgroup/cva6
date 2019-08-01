/*-
 * Copyright (c) 2018 Matthew Naylor
 * Copyright (c) 2018 Jonathan Woodruff
 * Copyright (c) 2018 Alexandre Joannou
 * Copyright (c) 2018 Hesham Almatary
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory (Department of Computer Science and
 * Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
 * DARPA SSITH research programme.
 *
 * This software was partly developed by the University of Cambridge
 * Computer Laboratory as part of the Partially-Ordered Event-Triggered
 * Systems (POETS) project, funded by EPSRC grant EP/N031768/1.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

#include <signal.h>

// API
////////////////////////////////////////////////////////////////////////////////

extern "C" {
    unsigned long long serv_socket_create(const char * name, unsigned int dflt_port);
    void serv_socket_init(unsigned long long ptr, sighandler_t handler);
    uint32_t serv_socket_get8(unsigned long long ptr);
    uint8_t serv_socket_put8(unsigned long long ptr, uint8_t byte);
    void serv_socket_getN(unsigned int* result, unsigned long long ptr, int nbytes);
    uint8_t serv_socket_putN(unsigned long long ptr, int nbytes, unsigned int* data);
    void broken_pipe_handler(int signum);
}
