//----------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2015 NVIDIA Corporation
// Copyright 2014 Cisco Systems, Inc.
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
// Title -- NODOCS -- TLM2 ports
//
// The following defines TLM2 port classes.
//
//----------------------------------------------------------------------

// class -- NODOCS -- uvm_tlm_b_transport_port
//
// Class providing the blocking transport port.
// The port can be bound to one export.
// There is no backward path for the blocking transport.

// @uvm-ieee 1800.2-2017 auto 12.3.6.1
class uvm_tlm_b_transport_port #(type T=uvm_tlm_generic_payload)
  extends uvm_port_base #(uvm_tlm_if #(T));
  `UVM_PORT_COMMON(`UVM_TLM_B_MASK, "uvm_tlm_b_transport_port")
  `UVM_TLM_B_TRANSPORT_IMP(this.m_if, T, t, delay)
endclass


// class -- NODOCS -- uvm_tlm_nb_transport_fw_port
//
// Class providing the non-blocking backward transport port.
// Transactions received from the producer, on the forward path, are
// sent back to the producer on the backward path using this
// non-blocking transport port.
// The port can be bound to one export.
//
  
// @uvm-ieee 1800.2-2017 auto 12.3.6.2
class uvm_tlm_nb_transport_fw_port #(type T=uvm_tlm_generic_payload,
                                 type P=uvm_tlm_phase_e)
  extends uvm_port_base #(uvm_tlm_if #(T,P));
  `UVM_PORT_COMMON(`UVM_TLM_NB_FW_MASK, "uvm_tlm_nb_transport_fw_port")
  `UVM_TLM_NB_TRANSPORT_FW_IMP(this.m_if, T, P, t, p, delay)
endclass

// class -- NODOCS -- uvm_tlm_nb_transport_bw_port
//
// Class providing the non-blocking backward transport port.
// Transactions received from the producer, on the forward path, are
// sent back to the producer on the backward path using this
// non-blocking transport port
// The port can be bound to one export.
//
  
// @uvm-ieee 1800.2-2017 auto 12.3.6.3
class uvm_tlm_nb_transport_bw_port #(type T=uvm_tlm_generic_payload,
                                 type P=uvm_tlm_phase_e)
  extends uvm_port_base #(uvm_tlm_if #(T,P));

   // Function -- NODOCS -- new
  `UVM_PORT_COMMON(`UVM_TLM_NB_BW_MASK, "uvm_tlm_nb_transport_bw_port")
  `UVM_TLM_NB_TRANSPORT_BW_IMP(this.m_if, T, P, t, p, delay)
endclass
