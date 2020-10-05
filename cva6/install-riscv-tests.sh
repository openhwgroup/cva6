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

if ! [ -n "$TESTS_REPO" ]; then
  TESTS_REPO="https://github.com/riscv/riscv-tests.git"
  TESTS_BRANCH="master"
  TESTS_HASH="f92842f91644092960ac7946a61ec2895e543cec"
fi
echo $TESTS_REPO
echo $TESTS_BRANCH
echo $TESTS_HASH

mkdir -p cva6/tests
if ! [ -d cva6/tests/riscv-tests ]; then
  git clone $TESTS_REPO -b $TESTS_BRANCH cva6/tests/riscv-tests
  cd cva6/tests/riscv-tests; git checkout $TESTS_HASH; 
  git submodule update --init --recursive
  git apply --directory=env ../../../cva6/riscv-tests-env.patch
  cd -
fi
