# Copyright 2022 Thales DIS SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./cva6/regress/install-cva6.sh
source ./cva6/regress/install-riscv-dv.sh

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv64a6_imafdc_sv39
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-uvm,spike
fi

if ! [ -n "$list_num" ]; then
  list_num=1 #default test list
fi

export cov=1 #enable the Code Coverage

cd cva6/sim/
dd=$(date '+%Y-%m-%d')
key_word="Mismatch[1]:"
#Read from the iss_regr.log to detect the failed tests
logfile=out_$dd/iss_regr.log      
j=0;
make clean_all
rm -rf out_$dd

if [[ "$list_num" = 0 ]];then
  TEST_NAME=(
           "riscv_arithmetic_basic_test"
           "riscv_unaligned_load_store_test"
           );
   I=(50 10);
   #this list re-use tests from the base_testlist in the riscv-dv
   #Just the tests in the riscv-dv YAML file
   TESTLIST_FILE=dv/yaml/base_testlist.yaml 
elif [[ "$list_num" = 1 ]];then
  TEST_NAME=(
           "riscv_arithmetic_basic_test_no_comp"
           "riscv_arithmetic_basic_illegal_test"
           "riscv_arithmetic_basic_illegal_hint_test"
           "riscv_arithmetic_basic_dret"
           );
   I=(50 10 10 20);
   TESTLIST_FILE=cva6_base_testlist.yaml 
elif [[ "$list_num" = 2 ]];then	
	TEST_NAME=(
           "riscv_arithmetic_basic_csr_test"
           "riscv_arithmetic_basic_hint_csr_test"
           "riscv_arithmetic_basic_rand_prvl"
           "riscv_arithmetic_basic_csr_dummy"
           );
	I=(100 100 40 20);
	TESTLIST_FILE=cva6_base_testlist.yaml
fi

if [[ ${#TEST_NAME[@]} != ${#I[@]} ]];then
  echo "***********ERROR***************"
  echo "The length of TEST_NAME and I should be equal !!!!"
  echo "Fix the length of one of the arrays"
  exit 
fi

printf "+====================================================================================+"
header="\n %-50s %-20s %s\n"
format=" %-50s %-20d %d\n"
printf "$header" "TEST NAME" "ITERATION" "BATCH SIZE"
printf "+====================================================================================+\n"

while [[ $j -lt ${#TEST_NAME[@]} ]];do
  printf "$format" \
  ${TEST_NAME[j]} ${I[j]} ${BZ[j]}
  j=$((j+1))
done
printf "+====================================================================================+\n"
j=0

while [[ $j -lt ${#TEST_NAME[@]} ]];do
  python3 cva6.py --testlist=$TESTLIST_FILE --test ${TEST_NAME[j]} --iss_yaml cva6.yaml --target $DV_TARGET --iss=vcs-uvm,spike -i ${I[j]} -bz 1 --iss_timeout 300
  n=0
  echo "Generate the test : ${TEST_NAME[j]}"
#this while loop detects the failed tests from the log file and remove them
  echo "Deleting failed tests : "
  while read line;do
    if [[ "$line" = "" ]];then
      n=$((n+1))
    fi
    for word in $line;do
      if [[ "$word" = "$key_word" ]];then
        echo -e ""${TEST_NAME[j]}"_"$n" : Failed"
        rm -rf vcs_results/default/vcs.d/simv.vdb/snps/coverage/db/testdata/"${TEST_NAME[j]}"_"$n"/
      fi
    done
  done < $logfile
  make clean_all
  rm -rf out_$dd
  j=$((j+1))
done
