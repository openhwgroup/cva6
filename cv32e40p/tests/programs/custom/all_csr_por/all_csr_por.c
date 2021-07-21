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
**
** Modeled CSR power-on-reset test:
**    Reads the CSRs modeled by the Imperas OVPsim Reference Model and prints
**    some useful (?) messages to stdout.  Will fail for one of two reasons:
**       1. Step-and-compare against RM mismatch.
**       2. read value does not match the documented PoR value.
**
** This is a manually written prototype of a (planned) generated test-program.
** The primary goals of this test-program is to get proof of life from all CV32E40P
** CSRs and asertain the status of CSR modeling in the OVPsim Reference Model.
** In this prototype, all addresses and expected values are hand-coded.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

#include "all_csr_por.h"

int main(int argc, char *argv[]) {
    printf("\n\nBegin Test\n");
	//
	// Encoding sopace is 12 bits, ie 0x000 to 0xFFF
	// Iterate to ensure that exceptions or values occur on every entry
	// and match between RM and RTL
	//
    read_csr();

    printf("End Test\n\n");

    return EXIT_SUCCESS;

}
