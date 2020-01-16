//
//------------------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2015-2018 NVIDIA Corporation
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

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_push_driver #(REQ,RSP)
//
// Base class for a driver that passively receives transactions, i.e. does not
// initiate requests transactions. Also known as ~push~ mode. Its ports are
// typically connected to the corresponding ports in a push sequencer as follows:
//
//|  push_sequencer.req_port.connect(push_driver.req_export);
//|  push_driver.rsp_port.connect(push_sequencer.rsp_export);
//
// The ~rsp_port~ needs connecting only if the driver will use it to write
// responses to the analysis export in the sequencer.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 13.8.1
class uvm_push_driver #(type REQ=uvm_sequence_item,
                        type RSP=REQ) extends uvm_component;

  `uvm_component_param_utils(uvm_push_driver#(REQ,RSP))
  `uvm_type_name_decl("uvm_push_driver #(REQ,RSP)")
  
  // Port -- NODOCS -- req_export
  //
  // This export provides the blocking put interface whose default 
  // implementation produces an error. Derived drivers must override ~put~
  // with an appropriate implementation (and not call super.put). Ports
  // connected to this export will supply the driver with transactions.

  uvm_blocking_put_imp #(REQ, uvm_push_driver #(REQ,RSP)) req_export;

  // Port -- NODOCS -- rsp_port
  //
  // This analysis port is used to send response transactions back to the
  // originating sequencer.

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
    req_export = new("req_export", this);
    rsp_port   = new("rsp_port", this);
  endfunction

  function void check_port_connections();
    if (req_export.size() != 1)
    uvm_report_fatal("Connection Error",
                     $sformatf("Must connect to seq_item_port(%0d)",
                               req_export.size()), UVM_NONE);
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    check_port_connections();
  endfunction
  
  virtual task put(REQ item);
    uvm_report_fatal("UVM_PUSH_DRIVER", "Put task for push driver is not implemented", UVM_NONE);
  endtask

endclass
