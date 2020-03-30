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
** Smoke test for the CV32E40P core.  Prints and quits
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    /* Print a banner to stdout and die */
    printf("\nThis is the OpenHW Group CV32E40P RISC-V processor core.\n\n");
    return EXIT_SUCCESS;
}
