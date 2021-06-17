..
   Copyright (c) 2020 OpenHW Group

   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

   https://solderpad.org/licenses/

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


.. _planning_requirements:

Verification Planning and Requirements
======================================

A key activity of any verification effort is to capture a Verification
Plan (aka Test Plan or just testplan). This document is not that. The
purpose of a verification plan is to identify what features need to be
verified; the success criteria of the feature and the coverage metrics
for testing the feature.  Refer to
`Verification Planning 101 <https://github.com/openhwgroup/core-v-verif/blob/master/docs/VerifPlans/VerificationPlanning101.md>`_
for a tutorial on how verification planning of CORE-V IP is done.

The Verification Strategy (this document) exists to support the
Verification Plan. A trivial example illustrates this point: the
CV32E40P verification plan requires that all RV32I instructions be
generated and their results checked. In this case, the testbench needs to
have these capabilities and its the purpose of the Verification Strategy
document to explain how that is done.
