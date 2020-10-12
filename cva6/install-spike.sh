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

set -e
VERSION="59a9277ac1e3f9aca630fb035d1dbacaa091e375"

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if [ ! -f "$SPIKE_ROOT/bin/spike"  ]; then
    echo "Installing Spike"
    PATCH_DIR=`pwd`/cva6
    mkdir -p $SPIKE_ROOT
    cd $SPIKE_ROOT
    git clone https://github.com/riscv/riscv-isa-sim.git 
    cd riscv-isa-sim
    git checkout $VERSION
    git apply $PATCH_DIR/spike-shared-fesvr-lib.patch
    mkdir -p build
    cd build
    ../configure --enable-commitlog --prefix="$SPIKE_ROOT"
    make -j${NUM_JOBS}
    make install
else
    echo "Using Spike from cached directory."
fi



