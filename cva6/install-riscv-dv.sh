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

# riscv-dv env variables
export RISCV_TOOLCHAIN=$RISCV
if ! [ -n "$RISCV_GCC" ]; then
  export RISCV_GCC="$RISCV_TOOLCHAIN/bin/riscv-none-elf-gcc"
fi
if ! [ -n "$RISCV_OBJCOPY" ]; then
  export RISCV_OBJCOPY="$RISCV_TOOLCHAIN/bin/riscv-none-elf-objcopy"
fi
export SPIKE_PATH=$SPIKE_ROOT/bin
export RTL_PATH=$ROOT_PROJECT/core-v-cores/cva6
export TESTS_PATH=$ROOT_PROJECT/cva6/tests

if ! [ -n "$DV_REPO" ]; then
  export DV_REPO="https://github.com/ThalesGroup/riscv-dv.git"
  export DV_BRANCH="oss"
  export DV_HASH="8ff0a5ecb56269cfff94b59c9f7f4e267630ef20"
  export DV_PATCH=
fi
echo $DV_REPO
echo $DV_BRANCH
echo $DV_HASH
echo $DV_PATCH

mkdir -p uvm
if ! [ -d uvm/riscv-dv ]; then
  git clone $DV_REPO -b $DV_BRANCH uvm/riscv-dv
  cd uvm/riscv-dv; git checkout $DV_HASH; 
  if [ -f "$DV_PATCH" ]; then
    git apply $DV_PATCH
  fi
  cd -
fi

# install riscv-dv dependencies
cd uvm/riscv-dv; pip3 install -r requirements.txt; cd -
