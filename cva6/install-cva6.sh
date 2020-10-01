###############################################################################
#
# Copyright 2020 Thales DIS Design Services SAS
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
###############################################################################
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@invia.fr)
#
###############################################################################

# Customise this to a fast local disk
export ROOT_PROJECT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../" && pwd)
export TOP=$ROOT_PROJECT/tools

# where to install the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install Verilator 
if ! [ -n "$VERILATOR_ROOT" ]; then
  export VERILATOR_ROOT=$TOP/verilator-4.014/
fi
cva6/install-verilator.sh

export PATH=$RISCV/bin:$VERILATOR_ROOT/bin:$PATH
export LIBRARY_PATH=$RISCV/lib
export LD_LIBRARY_PATH=$RISCV/lib
export C_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include
export CPLUS_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include

# number of parallel jobs to use for make commands and simulation
export NUM_JOBS=24

# install the required tools for cva6
if ! [ -n "$CVA6_REPO" ]; then
  CVA6_REPO="https://github.com/ThalesGroup/cva6.git"
  CVA6_BRANCH="master-verif"
  CVA6_HASH="22f718c0f25e1abaae46aafe4b1760ff0be903d0"
  CVA6_PATCH=
fi
echo $CVA6_REPO
echo $CVA6_BRANCH
echo $CVA6_HASH
echo $CVA6_PATCH

if ! [ -d core-v-cores/cva6 ]; then
  git clone --recursive $CVA6_REPO -b $CVA6_BRANCH core-v-cores/cva6
  cd core-v-cores/cva6; git checkout $CVA6_HASH;
  if [ -f ../$CVA6_PATCH ]; then
    git apply ../$CVA6_PATCH
  fi
  cd -
fi

# install Spike
if ! [ -n "$SPIKE_ROOT" ]; then
  export SPIKE_ROOT=$TOP/spike/
fi
cva6/install-spike.sh
