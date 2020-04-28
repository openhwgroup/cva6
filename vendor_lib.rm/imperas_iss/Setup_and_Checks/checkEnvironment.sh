#!/bin/bash

which checkinstall.exe
if [ $? -ne 0 ]; then
  echo "# please ensure Imperas environment is setup"
  exit
fi

#
# Check IMPERAS Installation supports this example
#
checkinstall.exe -p install.pkg --nobanner || exit

#
# Is TARGET set?
#
if [ -z "$TARGET" ]; then
  echo "# Please set TARGET to QUESTA or INCISIVE or VCS or DSIM"

#
# Cadence Incisive
#
elif [ "$TARGET" = "INCISIVE" ]; then
  echo "# TARGET is INCISIVE"
  which ncsim
  if [ $? -ne 0 ]; then
    echo "# Cannot find ncsim on PATH, Please check environment for INSICIVE setup"
  fi
  which imc
  if [ $? -ne 0 ]; then
    echo "# Cannot find imc on PATH, Please check environment for INSICIVE setup, for coverage analysis"
  fi
  if [ -z $INCISIVE_HOME ] || [ ! -d $INCISIVE_HOME ]; then
    echo "# INCISIVE_HOME is not set or is not a valid directory"
  fi

#
# Mentor Questa
#
elif [ "$TARGET" = "QUESTA" ]; then
  echo "# TARGET is QUESTA"
  which vsim
  if [ $? -ne 0 ]; then
    echo "# Cannot find vsim on PATH, Please check environment for QUESTA setup"
  fi
  which vcover
  if [ $? -ne 0 ]; then
    echo "# Cannot find vcover on PATH, Please check environment for QUESTA setup, for coverage analysis"
  fi
  if [ -z $QUESTA_HOME ] || [ ! -d $QUESTA_HOME ]; then
    echo "# QUESTA_HOME is not set or is not a valid directory"
  fi

#
# Synopsys VCS
#
elif [ "$TARGET" = "VCS" ]; then
  echo "# TARGET is VCS"
  which vcs
  if [ $? -ne 0 ]; then
    echo "# Cannot find vcs on PATH, Please check environment for VCS setup"
  fi
  which urg
  if [ $? -ne 0 ]; then
    echo "# Cannot find urg on PATH, Please check environment for VCS setup, for coverage analysis"
  fi
  if [ -z $VCS_HOME ] || [ ! -d $VCS_HOME ]; then
    echo "# VCS_HOME is not set or is not a valid directory"
  fi

#
# Metrics DSim
#
elif [ "$TARGET" = "DSIM" ]; then
   echo "# TARGET is DSIM"
   which dsim
   if [ $? -ne 0 ]; then
     echo "# Cannot find dsim on PATH, Please check environment for DSIM setup"
   fi
   if [ -z $DSIM_HOME ] || [ ! -d $DSIM_HOME ]; then
     echo "# DSIM_HOME is not set or is not a valid directory"
   fi

#
# Not a recognized TARGET
#
else
  echo "# TARGET is $TARGET, this is not supported, Please set TARGET INCISIVE, QUESTA, VCS or DSIM"
fi
