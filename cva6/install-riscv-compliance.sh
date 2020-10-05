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

if ! [ -n "$COMPLIANCE_REPO" ]; then
  COMPLIANCE_REPO="https://github.com/riscv/riscv-compliance.git"
  COMPLIANCE_BRANCH="master"
  COMPLIANCE_HASH="220e78542da4510e40eac31e31fdd4e77cdae437"
  COMPLIANCE_PATCH="../../../cva6/riscv-compliance.patch"
fi
echo $COMPLIANCE_REPO
echo $COMPLIANCE_BRANCH
echo $COMPLIANCE_HASH
echo $COMPLIANCE_PATCH

mkdir -p cva6/tests
if ! [ -d cva6/tests/riscv-compliance ]; then
  git clone $COMPLIANCE_REPO -b $COMPLIANCE_BRANCH cva6/tests/riscv-compliance
  cd cva6/tests/riscv-compliance; git checkout $COMPLIANCE_HASH;
  if [ -f "$COMPLIANCE_PATCH" ]; then
    git apply $COMPLIANCE_PATCH
  fi
  cd -
fi
