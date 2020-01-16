//
//-----------------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2010-2013 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2011 AMD
// Copyright 2015 NVIDIA Corporation
// Copyright 2012 Accellera Systems Initiative
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
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Title -- NODOCS -- Sequence Item Pull Ports
//
// This section defines the port, export, and imp port classes for
// communicating sequence items between <uvm_sequencer #(REQ,RSP)> and
// <uvm_driver #(REQ,RSP)>.
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_seq_item_pull_port #(REQ,RSP)
//
// UVM provides a port, export, and imp connector for use in sequencer-driver
// communication. All have standard port connector constructors, except that
// uvm_seq_item_pull_port's default min_size argument is 0; it can be left
// unconnected.
//
//-----------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 15.2.2.1
class uvm_seq_item_pull_port #(type REQ=int, type RSP=REQ)
  extends uvm_port_base #(uvm_sqr_if_base #(REQ, RSP));
  `UVM_SEQ_PORT(`UVM_SEQ_ITEM_PULL_MASK, "uvm_seq_item_pull_port")
  `UVM_SEQ_ITEM_PULL_IMP(this.m_if, REQ, RSP, t, t)

  bit print_enabled;
    
endclass


//-----------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_seq_item_pull_export #(REQ,RSP)
//
// This export type is used in sequencer-driver communication. It has the
// standard constructor for exports.
//
//-----------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 15.2.2.2
class uvm_seq_item_pull_export #(type REQ=int, type RSP=REQ)
  extends uvm_port_base #(uvm_sqr_if_base #(REQ, RSP));
  `UVM_EXPORT_COMMON(`UVM_SEQ_ITEM_PULL_MASK, "uvm_seq_item_pull_export")
  `UVM_SEQ_ITEM_PULL_IMP(this.m_if, REQ, RSP, t, t)
endclass


//-----------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_seq_item_pull_imp #(REQ,RSP,IMP)
//
// This imp type is used in sequencer-driver communication. It has the
// standard constructor for imp-type ports.
//
//-----------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 15.2.2.3
class uvm_seq_item_pull_imp #(type REQ=int, type RSP=REQ, type IMP=int)
  extends uvm_port_base #(uvm_sqr_if_base #(REQ, RSP));
   // Function -- NODOCS -- new
  `UVM_IMP_COMMON(`UVM_SEQ_ITEM_PULL_MASK, "uvm_seq_item_pull_imp",IMP)
  `UVM_SEQ_ITEM_PULL_IMP(m_imp, REQ, RSP, t, t)

endclass
