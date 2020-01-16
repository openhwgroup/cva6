//
//------------------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2013 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2015-2018 NVIDIA Corporation
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
//------------------------------------------------------------------------------

typedef class uvm_sequence_item;

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_driver #(REQ,RSP)
//
// The base class for drivers that initiate requests for new transactions via
// a uvm_seq_item_pull_port. The ports are typically connected to the exports of
// an appropriate sequencer component.
//
// This driver operates in pull mode. Its ports are typically connected to the
// corresponding exports in a pull sequencer as follows:
//
//|    driver.seq_item_port.connect(sequencer.seq_item_export);
//|    driver.rsp_port.connect(sequencer.rsp_export);
//
// The ~rsp_port~ needs connecting only if the driver will use it to write
// responses to the analysis export in the sequencer.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 13.7.1
class uvm_driver #(type REQ=uvm_sequence_item,
                   type RSP=REQ) extends uvm_component;

  `uvm_component_param_utils(uvm_driver#(REQ,RSP))
  // TODO: Would it be useful to change this to:
  //| `uvm_type_name_decl($sformatf("uvm_driver #(%s,%s)", REQ::type_name(), RSP::type_name()))
  `uvm_type_name_decl("uvm_driver #(REQ,RSP)")

  // Port -- NODOCS -- seq_item_port
  //
  // Derived driver classes should use this port to request items from the
  // sequencer. They may also use it to send responses back.

  uvm_seq_item_pull_port #(REQ, RSP) seq_item_port;

  uvm_seq_item_pull_port #(REQ, RSP) seq_item_prod_if; // alias

  // Port -- NODOCS -- rsp_port
  //
  // This port provides an alternate way of sending responses back to the
  // originating sequencer. Which port to use depends on which export the
  // sequencer provides for connection.

  uvm_analysis_port #(RSP) rsp_port;

  REQ req;
  RSP rsp;

  // Function -- NODOCS -- new
  //
  // Creates and initializes an instance of this class using the normal
  // constructor arguments for <uvm_component>: ~name~ is the name of the
  // instance, and ~parent~ is the handle to the hierarchical parent, if any.

  function new (string name, uvm_component parent);
    super.new(name, parent);
    seq_item_port    = new("seq_item_port", this);
    rsp_port         = new("rsp_port", this);
    seq_item_prod_if = seq_item_port;
  endfunction // new

endclass
