#!/bin/bash

#default no batch mode
BATCHMODE=0


######################
# helper function
LIGHT_GREEN_COL="\033[1;32m"
LIGHT_RED_COL="\033[1;31m"
NO_COL="\033[0m"
function check_exitcode() {

    if [ $1 -ne 0 ] ; then
        echo -en "$LIGHT_RED_COL$2 [ FAILED ]$NO_COL \n";
        exit 1;
    else
        echo -en "$LIGHT_GREEN_COL$2 [ OK ]$NO_COL \n";
    fi
}
######################


######################
# check args,
# otherwise use default
######################
if [ $1 -eq 0 ]; then
BATCHMODE=1
fi

######################
#compile sourcefiles
######################

./compile.sh
check_exitcode $? "compile sources"
######################


######################
#start modelsim in batch mode
######################

if [ ${BATCHMODE} -eq 1 ] ; then
  vsim -c -t ps -do tb_nogui.do
else
  ######################
  #start modelsim normally
  ######################

  vsim -t 1ps -do tb.do
fi
