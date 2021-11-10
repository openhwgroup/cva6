/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
** Basic debugger test. Needs more work and bugs fixed
** It will launch a debug request and have debugger code execute (debugger.S)
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

extern volatile uint32_t test_debugger_entry;

#define MACHINE 3
int main(int argc, char *argv[])
{
    unsigned int check_reg;
    check_reg = test_debugger_entry;

    printf("Debug reg = %08x\n", check_reg);
    // Debug code will write 0xff to this register
    // If debug mode has not been entered, we will fail
    if ((check_reg & 0xff) == 0xa5) {
        return EXIT_SUCCESS;
    }
    else {
        return EXIT_FAILURE;
    }
}
