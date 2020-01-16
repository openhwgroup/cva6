//----------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2014-2015 NVIDIA Corporation
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
//----------------------------------------------------------------------

//----------------------------------------------------------------------
// Title -- NODOCS -- Interface Masks
//
// Each of the following macros is a mask that identifies which
// interfaces a particular port requires or export provides.  The
// interfaces are identified by bit position and can be OR'ed together
// for combination ports/exports.  The mask is used to do run-time
// interface type checking of port/export connections.
//----------------------------------------------------------------------

// MACRO -- NODOCS -- `UVM_TLM_NB_FW_MASK
//
// Define Non blocking Forward mask onehot assignment = 'b001
`define UVM_TLM_NB_FW_MASK  (1<<0)

// MACRO -- NODOCS -- `UVM_TLM_NB_BW_MASK
//
// Define Non blocking backward mask onehot assignment = 'b010
`define UVM_TLM_NB_BW_MASK  (1<<1)

// MACRO -- NODOCS -- `UVM_TLM_B_MASK
//
// Define blocking mask onehot assignment = 'b100
`define UVM_TLM_B_MASK      (1<<2)
