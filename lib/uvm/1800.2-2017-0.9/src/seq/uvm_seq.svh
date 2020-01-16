//
//------------------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2017 NVIDIA Corporation
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

`include "seq/uvm_sequence_item.svh"
`include "seq/uvm_sequencer_base.svh"
`include "seq/uvm_sequencer_analysis_fifo.svh"
`include "seq/uvm_sequencer_param_base.svh"
`include "seq/uvm_sequencer.svh"
`include "seq/uvm_push_sequencer.svh"
`include "seq/uvm_sequence_base.svh"
`include "seq/uvm_sequence.svh"
`include "seq/uvm_sequence_library.svh"

typedef uvm_sequence  #(uvm_sequence_item, uvm_sequence_item) uvm_default_sequence_type;
typedef uvm_sequencer #(uvm_sequence_item, uvm_sequence_item) uvm_default_sequencer_type;
typedef uvm_driver    #(uvm_sequence_item, uvm_sequence_item) uvm_default_driver_type;
typedef uvm_sequencer_param_base #(uvm_sequence_item, uvm_sequence_item) uvm_default_sequencer_param_type;
