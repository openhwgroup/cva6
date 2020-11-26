#!/bin/bash

###############################################################################
#
# Copyright 2020 OpenHW Group
# 
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     https://solderpad.org/licenses/
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# 
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################

#printf "\n\nCompare to reference files ... \n\n";
FAIL=0
RUN=0

#for ref in ${SUITEDIR}/references/*.reference_output;
#do 
#    base=$(basename ${ref})
#    stub=${base//".reference_output"/}
#    sig=${WORK}/${RISCV_ISA}/${stub}.signature.output
#
#    RUN=$((${RUN} + 1))
    
    #
    # Ensure both files exist
    #
    if [ -f ${REF} ] && [ -f ${SIG} ]; then 
        echo -n "Check $(printf %24s ${COMPL_PROG})"
        RUN=$((${RUN} + 1))
    else
        echo    "Check $(printf %24s ${COMPL_PROG}) ... IGNORE"
#        continue
    fi
    diff --ignore-case --strip-trailing-cr ${REF} ${SIG} #&> /dev/null
    if [ $? == 0 ]
    then
        echo " ... OK"
    else
        echo " ... FAIL"
        FAIL=$((${FAIL} + 1))
    fi
#done

# warn on missing reverse reference
#for sig in ${WORK}/${RISCV_ISA}/*.signature.output; 
#do
#    base=$(basename ${sig})
#    stub=${base//".signature.output"/}
#    ref=${SUITEDIR}/references/${stub}.reference_output
#
#    if [ -f $sig ] && [ ! -f ${ref} ]; then
#        echo "Error: sig ${sig} no corresponding ${ref}"
#        FAIL=$((${FAIL} + 1))
#    fi
#done

declare -i status=0
if [ ${FAIL} == 0 ]; then
    echo "--------------------------------"
    echo -n "OK: ${RUN}/${RUN} "
    status=0
else
    echo "--------------------------------"
    echo -n "FAIL: ${FAIL}/${RUN} "
    status=1
fi
echo "RISCV_TARGET=${RISCV_TARGET} RISCV_DEVICE=${RISCV_DEVICE} RISCV_ISA=${RISCV_ISA}"
echo
exit ${status}
