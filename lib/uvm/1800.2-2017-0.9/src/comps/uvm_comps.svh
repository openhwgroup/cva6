//
//------------------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2017 Cisco Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------------------------

 `include "comps/uvm_pair.svh"
 `include "comps/uvm_policies.svh"
 `include "comps/uvm_in_order_comparator.svh"
 `include "comps/uvm_algorithmic_comparator.svh"
 `ifdef UVM_ENABLE_DEPRECATED_API
    `include "comps/uvm_random_stimulus.svh"
 `endif
 `include "comps/uvm_subscriber.svh"

 `include "comps/uvm_monitor.svh"
 `include "comps/uvm_driver.svh"
 `include "comps/uvm_push_driver.svh"
 `include "comps/uvm_scoreboard.svh" 
 `include "comps/uvm_agent.svh"
 `include "comps/uvm_env.svh"
 `include "comps/uvm_test.svh"
