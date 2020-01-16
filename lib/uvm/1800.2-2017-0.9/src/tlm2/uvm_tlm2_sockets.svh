//----------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
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
//----------------------------------------------------------------------

//----------------------------------------------------------------------
// Title -- NODOCS -- TLM Sockets
//
// Each uvm_tlm_*_socket class is derived from a corresponding
// uvm_tlm_*_socket_base class.  The base class contains most of the
// implementation of the class, The derived classes (in this file)
// contain the connection semantics.
//
// Sockets come in several flavors: Each socket is either an initiator or a 
// target, a pass-through or a terminator. Further, any particular socket 
// implements either the blocking interfaces or the nonblocking interfaces. 
// Terminator sockets are used on initiators and targets as well as 
// interconnect components as shown in the figure above. Pass-through
//  sockets are used to enable connections to cross hierarchical boundaries.
//
// There are eight socket types: the cross of blocking and nonblocking,
// pass-through and termination, target and initiator
//
// Sockets are specified based on what they are (IS-A)
// and what they contains (HAS-A).
// IS-A and HAS-A are types of object relationships. 
// IS-A refers to the inheritance relationship and
//  HAS-A refers to the ownership relationship. 
// For example if you say D is a B that means that D is derived from base B. 
// If you say object A HAS-A B that means that B is a member of A.
//----------------------------------------------------------------------


//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_b_initiator_socket
//
// IS-A forward port; has no backward path except via the payload
// contents
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 12.3.5.2.1
class uvm_tlm_b_initiator_socket #(type T=uvm_tlm_generic_payload)
                           extends uvm_tlm_b_initiator_socket_base #(T);


  // @uvm-ieee 1800.2-2017 auto 12.3.5.2.3
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction 
   

  // @uvm-ieee 1800.2-2017 auto 12.3.5.2.4
  function void connect(this_type provider);

    uvm_tlm_b_passthrough_initiator_socket_base #(T) initiator_pt_socket;
    uvm_tlm_b_passthrough_target_socket_base #(T) target_pt_socket;
    uvm_tlm_b_target_socket_base #(T) target_socket;

    uvm_component c;

    super.connect(provider);

    if($cast(initiator_pt_socket, provider)  ||
       $cast(target_pt_socket, provider)     ||
       $cast(target_socket, provider))
      return;

    c = get_comp();
    `uvm_error_context(get_type_name(),
       "type mismatch in connect -- connection cannot be completed", c)

  endfunction

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_b_target_socket
//
// IS-A forward imp; has no backward path except via the payload
// contents.
//
// The component instantiating this socket must implement
// a b_transport() method with the following signature
//
//|   task b_transport(T t, uvm_tlm_time delay);
//
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 12.3.5.1.1
class uvm_tlm_b_target_socket #(type IMP=int,
                                type T=uvm_tlm_generic_payload)
  extends uvm_tlm_b_target_socket_base #(T);

  local IMP m_imp;


  // @uvm-ieee 1800.2-2017 auto 12.3.5.1.3
  function new (string name, uvm_component parent, IMP imp = null);
    super.new (name, parent);
    if (imp == null) $cast(m_imp, parent);
    else m_imp = imp;
    if (m_imp == null)
       `uvm_error("UVM/TLM2/NOIMP", {"b_target socket ", name,
                                     " has no implementation"})
  endfunction


  // @uvm-ieee 1800.2-2017 auto 12.3.5.1.4
  function void connect(this_type provider);

    uvm_component c;

    super.connect(provider);

    c = get_comp();
    `uvm_error_context(get_type_name(),
       "You cannot call connect() on a target termination socket", c)
  endfunction

  `UVM_TLM_B_TRANSPORT_IMP(m_imp, T, t, delay)

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_initiator_socket
//
// IS-A forward port; HAS-A backward imp
//
// The component instantiating this socket must implement
// a nb_transport_bw() method with the following signature
//
//|   function uvm_tlm_sync_e nb_transport_bw(T t, ref P p, input uvm_tlm_time delay);
//
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 12.3.5.4.1
class uvm_tlm_nb_initiator_socket #(type IMP=int,
                                    type T=uvm_tlm_generic_payload,
                                    type P=uvm_tlm_phase_e)
  extends uvm_tlm_nb_initiator_socket_base #(T,P);

  uvm_tlm_nb_transport_bw_imp #(T,P,IMP) bw_imp;


  // @uvm-ieee 1800.2-2017 auto 12.3.5.4.3
  function new(string name, uvm_component parent, IMP imp = null);
    super.new (name, parent);
    if (imp == null) $cast(imp, parent);
    if (imp == null)
       `uvm_error("UVM/TLM2/NOIMP", {"nb_initiator socket ", name,
                                     " has no implementation"})
    bw_imp = new("bw_imp", imp);
  endfunction


   // @uvm-ieee 1800.2-2017 auto 12.3.5.4.4
   function void connect(this_type provider);

    uvm_tlm_nb_passthrough_initiator_socket_base #(T,P) initiator_pt_socket;
    uvm_tlm_nb_passthrough_target_socket_base #(T,P) target_pt_socket;
    uvm_tlm_nb_target_socket_base #(T,P) target_socket;

    uvm_component c;

    super.connect(provider);

    if($cast(initiator_pt_socket, provider)) begin
      initiator_pt_socket.bw_export.connect(bw_imp);
      return;
    end
    if($cast(target_pt_socket, provider)) begin
      target_pt_socket.bw_port.connect(bw_imp);
      return;
    end

    if($cast(target_socket, provider)) begin
      target_socket.bw_port.connect(bw_imp);
      return;
    end
    
    c = get_comp();
    `uvm_error_context(get_type_name(),
        "type mismatch in connect -- connection cannot be completed", c)

  endfunction

endclass


//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_target_socket
//
// IS-A forward imp; HAS-A backward port
//
// The component instantiating this socket must implement
// a nb_transport_fw() method with the following signature
//
//|   function uvm_tlm_sync_e nb_transport_fw(T t, ref P p, input uvm_tlm_time delay);
//
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 12.3.5.3.1
class uvm_tlm_nb_target_socket #(type IMP=int,
                                 type T=uvm_tlm_generic_payload,
                                 type P=uvm_tlm_phase_e)
  extends uvm_tlm_nb_target_socket_base #(T,P);

  local IMP m_imp;


  // @uvm-ieee 1800.2-2017 auto 12.3.5.3.3
  function new (string name, uvm_component parent, IMP imp = null);
    super.new (name, parent);
    if (imp == null) $cast(m_imp, parent);
    else m_imp = imp;
    bw_port = new("bw_port", get_comp());
    if (m_imp == null)
       `uvm_error("UVM/TLM2/NOIMP", {"nb_target socket ", name,
                                     " has no implementation"})
  endfunction


  // @uvm-ieee 1800.2-2017 auto 12.3.5.3.4
  function void connect(this_type provider);

    uvm_component c;

    super.connect(provider);

    c = get_comp();
    `uvm_error_context(get_type_name(),
       "You cannot call connect() on a target termination socket", c)
  endfunction

  `UVM_TLM_NB_TRANSPORT_FW_IMP(m_imp, T, P, t, p, delay)

endclass


//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_b_passthrough_initiator_socket
//
// IS-A forward port;
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 12.3.5.7
class uvm_tlm_b_passthrough_initiator_socket #(type T=uvm_tlm_generic_payload)
  extends uvm_tlm_b_passthrough_initiator_socket_base #(T);

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

   // Function  -- NODOCS -- connect
   //
   // Connect this socket to the specified <uvm_tlm_b_target_socket>
  function void connect(this_type provider);

    uvm_tlm_b_passthrough_initiator_socket_base #(T) initiator_pt_socket;
    uvm_tlm_b_passthrough_target_socket_base #(T) target_pt_socket;
    uvm_tlm_b_target_socket_base #(T) target_socket;

    uvm_component c;

    super.connect(provider);

    if($cast(initiator_pt_socket, provider) ||
       $cast(target_pt_socket, provider)    ||
       $cast(target_socket, provider))
      return;

    c = get_comp();
    `uvm_error_context(get_type_name(), "type mismatch in connect -- connection cannot be completed", c)

  endfunction

endclass


// @uvm-ieee 1800.2-2017 auto 12.3.5.8
class uvm_tlm_b_passthrough_target_socket #(type T=uvm_tlm_generic_payload)
  extends uvm_tlm_b_passthrough_target_socket_base #(T);

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction 
   
   // Function  -- NODOCS -- connect
   //
   // Connect this socket to the specified <uvm_tlm_b_initiator_socket>
  function void connect(this_type provider);

    uvm_tlm_b_passthrough_target_socket_base #(T) target_pt_socket;
    uvm_tlm_b_target_socket_base #(T) target_socket;

    uvm_component c;

    super.connect(provider);

    if($cast(target_pt_socket, provider)    ||
       $cast(target_socket, provider))
      return;

    c = get_comp();
    `uvm_error_context(get_type_name(),
       "type mismatch in connect -- connection cannot be completed", c)
  endfunction

endclass



//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_passthrough_initiator_socket
//
// IS-A forward port; HAS-A backward export
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 12.3.5.5
class uvm_tlm_nb_passthrough_initiator_socket #(type T=uvm_tlm_generic_payload,
                                             type P=uvm_tlm_phase_e)
  extends uvm_tlm_nb_passthrough_initiator_socket_base #(T,P);

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

   // Function  -- NODOCS -- connect
   //
   // Connect this socket to the specified <uvm_tlm_nb_target_socket>
  function void connect(this_type provider);

    uvm_tlm_nb_passthrough_initiator_socket_base #(T,P) initiator_pt_socket;
    uvm_tlm_nb_passthrough_target_socket_base #(T,P) target_pt_socket;
    uvm_tlm_nb_target_socket_base #(T,P) target_socket;

    uvm_component c;

    super.connect(provider);

    if($cast(initiator_pt_socket, provider)) begin
      bw_export.connect(initiator_pt_socket.bw_export);
      return;
    end

    if($cast(target_pt_socket, provider)) begin
      target_pt_socket.bw_port.connect(bw_export);
      return;
    end

    if($cast(target_socket, provider)) begin
      target_socket.bw_port.connect(bw_export);
      return;
    end

    c = get_comp();
    `uvm_error_context(get_type_name(),
       "type mismatch in connect -- connection cannot be completed", c)

  endfunction

endclass

//----------------------------------------------------------------------
// Class -- NODOCS -- uvm_tlm_nb_passthrough_target_socket
//
// IS-A forward export; HAS-A backward port
//----------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 12.3.5.6.1
class uvm_tlm_nb_passthrough_target_socket #(type T=uvm_tlm_generic_payload,
                                          type P=uvm_tlm_phase_e)
  extends uvm_tlm_nb_passthrough_target_socket_base #(T,P);

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction


  // @uvm-ieee 1800.2-2017 auto 12.3.5.6.2
  function void connect(this_type provider);

    uvm_tlm_nb_passthrough_target_socket_base #(T,P) target_pt_socket;
    uvm_tlm_nb_target_socket_base #(T,P) target_socket;

    uvm_component c;

    super.connect(provider);

    if($cast(target_pt_socket, provider)) begin
      target_pt_socket.bw_port.connect(bw_port);
      return;
    end

    if($cast(target_socket, provider)) begin
      target_socket.bw_port.connect(bw_port);
      return;
    end

    c = get_comp();
    `uvm_error_context(get_type_name(),
       "type mismatch in connect -- connection cannot be completed", c)

  endfunction

endclass

