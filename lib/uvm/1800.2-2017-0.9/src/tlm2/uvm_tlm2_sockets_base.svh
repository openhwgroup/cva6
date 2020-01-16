//----------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2011-2018 Cadence Design Systems, Inc.
// Copyright 2015 NVIDIA Corporation
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
// Title -- NODOCS -- TLM Socket Base Classes
//
// A collection of base classes, one for each socket type.  The reason
// for having a base class for each socket is that all the socket (base)
// types must be known before connect is defined.  Socket connection
// semantics are provided in the derived classes, which are user
// visible.
//
// Termination Sockets - A termination socket must be the terminus
// of every TLM path.  A transaction originates with an initiator socket
// and ultimately ends up in a target socket.  There may be zero or more
// pass-through sockets between initiator and target.
//
// Pass-through Sockets - Pass-through initiators are ports and contain
// exports for instance IS-A port and HAS-A export. Pass-through targets
// are the opposite, they are exports and contain ports.
//----------------------------------------------------------------------


//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_b_target_socket_base
//
// IS-A forward imp; has no backward path except via the payload
// contents.
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual
`endif
class uvm_tlm_b_target_socket_base #(type T=uvm_tlm_generic_payload)
  extends uvm_port_base #(uvm_tlm_if #(T));

  function new (string name, uvm_component parent);
    super.new (name, parent, UVM_IMPLEMENTATION, 1, 1);
    m_if_mask = `UVM_TLM_B_MASK;
  endfunction

  `UVM_TLM_GET_TYPE_NAME("uvm_tlm_b_target_socket")

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_b_initiator_socket_base
//
// IS-A forward port; has no backward path except via the payload
// contents
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual
`endif
class uvm_tlm_b_initiator_socket_base #(type T=uvm_tlm_generic_payload)
  extends uvm_port_base #(uvm_tlm_if #(T));

  `UVM_PORT_COMMON(`UVM_TLM_B_MASK, "uvm_tlm_b_initiator_socket")
  `UVM_TLM_B_TRANSPORT_IMP(this.m_if, T, t, delay)

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_target_socket_base
//
// IS-A forward imp; HAS-A backward port
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual
`endif
class uvm_tlm_nb_target_socket_base #(type T=uvm_tlm_generic_payload,
                                   type P=uvm_tlm_phase_e)
  extends uvm_port_base #(uvm_tlm_if #(T,P));

  uvm_tlm_nb_transport_bw_port #(T,P) bw_port;

  function new (string name, uvm_component parent);
    super.new (name, parent, UVM_IMPLEMENTATION, 1, 1);
    m_if_mask = `UVM_TLM_NB_FW_MASK;
  endfunction

  `UVM_TLM_GET_TYPE_NAME("uvm_tlm_nb_target_socket")

  `UVM_TLM_NB_TRANSPORT_BW_IMP(bw_port, T, P, t, p, delay)

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_initiator_socket_base
//
// IS-A forward port; HAS-A backward imp
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual 
`endif
class uvm_tlm_nb_initiator_socket_base #(type T=uvm_tlm_generic_payload,
                                      type P=uvm_tlm_phase_e)
  extends uvm_port_base #(uvm_tlm_if #(T,P));

  function new (string name, uvm_component parent);
    super.new (name, parent, UVM_PORT, 1, 1);
    m_if_mask = `UVM_TLM_NB_FW_MASK;
  endfunction

  `UVM_TLM_GET_TYPE_NAME("uvm_tlm_nb_initiator_socket")

  `UVM_TLM_NB_TRANSPORT_FW_IMP(this.m_if, T, P, t, p, delay)

endclass




//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_passthrough_initiator_socket_base
//
// IS-A forward port; HAS-A backward export
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual
`endif
class uvm_tlm_nb_passthrough_initiator_socket_base #(type T=uvm_tlm_generic_payload,
                                                  type P=uvm_tlm_phase_e)
  extends uvm_port_base #(uvm_tlm_if #(T,P));

  uvm_tlm_nb_transport_bw_export #(T,P) bw_export;

  function new (string name, uvm_component parent,
                int min_size=1, int max_size=1);
    super.new (name, parent, UVM_PORT, min_size, max_size);
    m_if_mask = `UVM_TLM_NB_FW_MASK;
    bw_export = new("bw_export", get_comp());
  endfunction

  `UVM_TLM_GET_TYPE_NAME("uvm_tlm_nb_passthrough_initiator_socket")

  `UVM_TLM_NB_TRANSPORT_FW_IMP(this.m_if, T, P, t, p, delay)
  `UVM_TLM_NB_TRANSPORT_BW_IMP(bw_export, T, P, t, p, delay)

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_passthrough_target_socket_base
//
// IS-A forward export; HAS-A backward port
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual 
`endif
class uvm_tlm_nb_passthrough_target_socket_base #(type T=uvm_tlm_generic_payload,
                                               type P=uvm_tlm_phase_e)
  extends uvm_port_base #(uvm_tlm_if #(T,P));

  uvm_tlm_nb_transport_bw_port #(T,P) bw_port;

  function new (string name, uvm_component parent,
                int min_size=1, int max_size=1);
    super.new (name, parent, UVM_EXPORT, min_size, max_size);
    m_if_mask = `UVM_TLM_NB_FW_MASK;
    bw_port = new("bw_port", get_comp());
  endfunction

  `UVM_TLM_GET_TYPE_NAME("uvm_tlm_nb_passthrough_target_socket")

  `UVM_TLM_NB_TRANSPORT_FW_IMP(this.m_if, T, P, t, p, delay)
  `UVM_TLM_NB_TRANSPORT_BW_IMP(bw_port, T, P, t, p, delay)

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_b_passthrough_initiator_socket_base
//
// IS-A forward port
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual 
`endif
class uvm_tlm_b_passthrough_initiator_socket_base #(type T=uvm_tlm_generic_payload)
  extends uvm_port_base #(uvm_tlm_if #(T));

  `UVM_PORT_COMMON(`UVM_TLM_B_MASK, "uvm_tlm_b_passthrough_initiator_socket")
  `UVM_TLM_B_TRANSPORT_IMP(this.m_if, T, t, delay)

endclass


//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_b_passthrough_target_socket_base
//
// IS-A forward export
//----------------------------------------------------------------------
`ifndef UVM_ENABLE_DEPRECATED_API
virtual 
`endif
class uvm_tlm_b_passthrough_target_socket_base #(type T=uvm_tlm_generic_payload)
  extends uvm_port_base #(uvm_tlm_if #(T));

  `UVM_EXPORT_COMMON(`UVM_TLM_B_MASK, "uvm_tlm_b_passthrough_target_socket")
  `UVM_TLM_B_TRANSPORT_IMP(this.m_if, T, t, delay)

 endclass
