/*
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */


#include <stdio.h>
#include <string.h>

#include "support.h"

extern char _test_stdout;

//
// Redefine standard write function
// arg0 FD, arg1 PTR, arg2 len
//
int _write (int fd, char *ptr, int len) {
    char *p = ptr;
    int i;

    for (i=0; i<len; i++) {
        _test_stdout = *p++;
    }
}

int _traphandlerC () {
    const char *message = "Traphandler Called\n";
    const char *ptr = message;
    _write(0, (char*)message, strlen(message));
    return 0;
}

void enableINT() {
    asm(
            "    csrr      t0, mie           \n"
            "    li        t1, (0x1 << 11)   \n"
            "    or        t1, t1, t0        \n"
            "    csrw      mie, t1           \n"
            "    csrr      t0, mstatus       \n"
            "    li        t1, (0x1 << 3)    \n"
            "    or        t1, t1, t0        \n"
            "    csrw      mstatus, t1       \n"
    );
    return;
}

void enableVEC() {
    asm(
        "    csrr      t0, mstatus       \n"
        "    li        t1, (0x1 << 23)   \n"
        "    or        t1, t1, t0        \n"
        "    csrw      mstatus, t1       \n"
    );
    return;
}

void setupVEC() {
    asm(".word 0x00b7f2d7 \n");
    return;
}
