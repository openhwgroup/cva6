//
//------------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2014 Semifore
// Copyright 2014 Intel Corporation
// Copyright 2010-2014 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2017 NVIDIA Corporation
// Copyright 2012-2017 Cisco Systems, Inc.
// Copyright 2017 Verific
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the "License"); you may not
//   use this file except in compliance with the License.  You may obtain a copy
//   of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
//   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
//   License for the specific language governing permissions and limitations
//   under the License.
//------------------------------------------------------------------------------

const int UVM_UNBOUNDED_CONNECTIONS = -1;
const string s_connection_error_id = "Connection Error";
const string s_connection_warning_id = "Connection Warning";
const string s_spaces = "                       ";

typedef class uvm_port_component_base;
typedef uvm_port_component_base uvm_port_list[string];


// TITLE -- NODOCS -- Port Base Classes
//


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_port_component_base
//
//------------------------------------------------------------------------------
// This class defines an interface for obtaining a port's connectivity lists
// after or during the end_of_elaboration phase.  The sub-class,
// <uvm_port_component #(PORT)>, implements this interface.
//
// Each port's full name and type name can be retrieved using ~get_full_name~ 
// and ~get_type_name~ methods inherited from <uvm_component>.
//------------------------------------------------------------------------------

virtual class uvm_port_component_base extends uvm_component;
   
  function new (string name, uvm_component parent);
    super.new(name,parent);
  endfunction

  // Function -- NODOCS -- is_port
  //
  pure virtual function bit is_port();

  // Function -- NODOCS -- is_export
  //
  pure virtual function bit is_export();

  // Function -- NODOCS -- is_imp
  //
  // These function determine the type of port. The functions are
  // mutually exclusive; one will return 1 and the other two will
  // return 0.

  pure virtual function bit is_imp();

  // Turn off auto config by not calling build_phase()
  virtual function bit use_automatic_config();
    return 0;
  endfunction : use_automatic_config    
   
  virtual task do_task_phase (uvm_phase phase);
  endtask
endclass


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_port_component #(PORT)
//
//------------------------------------------------------------------------------
// See description of <uvm_port_component_base> for information about this class
//------------------------------------------------------------------------------


class uvm_port_component #(type PORT=uvm_object) extends uvm_port_component_base;
  
  PORT m_port;

  function new (string name, uvm_component parent, PORT port);
    super.new(name,parent);
    if (port == null)
      uvm_report_fatal("Bad usage", "Null handle to port", UVM_NONE);
    m_port = port;
  endfunction

  virtual function string get_type_name();
    if(m_port == null) return "uvm_port_component";
    return m_port.get_type_name();
  endfunction
    
  virtual function void resolve_bindings();
    m_port.resolve_bindings();
  endfunction
  
  // Function -- NODOCS -- get_port
  //
  // Retrieve the actual port object that this proxy refers to.

  function PORT get_port();
    return m_port;
  endfunction

  function bit is_port ();
    return m_port.is_port();
  endfunction

  function bit is_export ();
    return m_port.is_export();
  endfunction

  function bit is_imp ();
    return m_port.is_imp();
  endfunction

endclass


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_port_base #(IF)
//
//------------------------------------------------------------------------------
//
// Transaction-level communication between components is handled via its ports,
// exports, and imps, all of which derive from this class.
//
// The uvm_port_base extends IF, which is the type of the interface implemented
// by derived port, export, or implementation. IF is also a type parameter to
// uvm_port_base.
//
//   IF  - The interface type implemented by the subtype to this base port
//
// The UVM provides a complete set of ports, exports, and imps for the OSCI-
// standard TLM interfaces. They can be found in the ../src/tlm/ directory.
// For the TLM interfaces, the IF parameter is always <uvm_tlm_if_base #(T1,T2)>.
//
// Just before <uvm_component::end_of_elaboration_phase>, an internal
// <uvm_component::resolve_bindings> process occurs, after which each port and
// export holds a list of all imps connected to it via hierarchical connections
// to other ports and exports. In effect, we are collapsing the port's fanout,
// which can span several levels up and down the component hierarchy, into a
// single array held local to the port. Once the list is determined, the port's
// min and max connection settings can be checked and enforced.
//
// uvm_port_base possesses the properties of components in that they have a
// hierarchical instance path and parent. Because SystemVerilog does not support
// multiple inheritance, uvm_port_base cannot extend both the interface it
// implements and <uvm_component>. Thus, uvm_port_base contains a local instance
// of uvm_component, to which it delegates such commands as get_name,
// get_full_name, and get_parent.
// The connectivity lists are returned in the form of handles to objects of this
// type. This allowing traversal of any port's fan-out and fan-in network
// through recursive calls to <get_connected_to> and <get_provided_to>. 
//
//------------------------------------------------------------------------------

// Class: uvm_port_base
// The library implements the following public API beyond what is documented
// in 1800.2.

// @uvm-ieee 1800.2-2017 auto 5.5.1
virtual class uvm_port_base #(type IF=uvm_void) extends IF;
   

  typedef uvm_port_base #(IF) this_type;
  
  // local, protected, and non-user properties
  protected int unsigned  m_if_mask;
  protected this_type     m_if;    // REMOVE
  protected int unsigned  m_def_index;
  uvm_port_component #(this_type) m_comp;
  local this_type m_provided_by[string];
  local this_type m_provided_to[string];
  local uvm_port_type_e   m_port_type;
  local int               m_min_size;
  local int               m_max_size;
  local bit               m_resolved;
  local this_type         m_imp_list[string];

  // Function -- NODOCS -- new
  //
  // The first two arguments are the normal <uvm_component> constructor
  // arguments.
  //
  // The ~port_type~ can be one of <UVM_PORT>, <UVM_EXPORT>, or
  // <UVM_IMPLEMENTATION>.
  //
  // The ~min_size~ and ~max_size~ specify the minimum and maximum number of
  // implementation (imp) ports that must be connected to this port base by the
  // end of elaboration. Setting ~max_size~ to ~UVM_UNBOUNDED_CONNECTIONS~ sets no
  // maximum, i.e., an unlimited number of connections are allowed.
  //
  // By default, the parent/child relationship of any port being connected to
  // this port is not checked. This can be overridden by configuring the
  // port's ~check_connection_relationships~ bit via ~uvm_config_int::set()~. See
  // <connect> for more information.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.1
  function new (string name,
                uvm_component parent,
                uvm_port_type_e port_type,
                int min_size=0,
                int max_size=1);
    uvm_component comp;
    int tmp;
    m_port_type = port_type;
    m_min_size  = min_size;
    m_max_size  = max_size;
    m_comp = new(name, parent, this);

    if (!uvm_config_int::get(m_comp, "", "check_connection_relationships",tmp))
      m_comp.set_report_id_action(s_connection_warning_id, UVM_NO_ACTION);

  endfunction


  // Function -- NODOCS -- get_name
  //
  // Returns the leaf name of this port. 

  // @uvm-ieee 1800.2-2017 auto 5.5.2.2
  function string get_name();
    return m_comp.get_name();
  endfunction


  // Function -- NODOCS -- get_full_name
  //
  // Returns the full hierarchical name of this port. 

  // @uvm-ieee 1800.2-2017 auto 5.5.2.3
  virtual function string get_full_name();
    return m_comp.get_full_name();
  endfunction


  // Function -- NODOCS -- get_parent
  //
  // Returns the handle to this port's parent, or ~null~ if it has no parent.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.4
  virtual function uvm_component get_parent();
    return m_comp.get_parent();
  endfunction


  // Function -- NODOCS -- get_comp
  //
  // Returns a handle to the internal proxy component representing this port.
  //
  // Ports are considered components. However, they do not inherit
  // <uvm_component>. Instead, they contain an instance of
  // <uvm_port_component #(PORT)> that serves as a proxy to this port.

  virtual function uvm_port_component_base get_comp();
    return m_comp;
  endfunction


  // Function -- NODOCS -- get_type_name
  //
  // Returns the type name to this port. Derived port classes must implement
  // this method to return the concrete type. Otherwise, only a generic
  // "uvm_port", "uvm_export" or "uvm_implementation" is returned.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.5
  virtual function string get_type_name();
    case( m_port_type )
      UVM_PORT : return "port";
      UVM_EXPORT : return "export";
      UVM_IMPLEMENTATION : return "implementation";
    endcase
  endfunction


  // Function -- NODOCS -- min_size
  //
  // Returns the minimum number of implementation ports that must
  // be connected to this port by the end_of_elaboration phase.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.7
  function int max_size ();
    return m_max_size;
  endfunction


  // Function -- NODOCS -- max_size
  //
  // Returns the maximum number of implementation ports that must
  // be connected to this port by the end_of_elaboration phase.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.6
  function int min_size ();
    return m_min_size;
  endfunction


  // Function -- NODOCS -- is_unbounded
  //
  // Returns 1 if this port has no maximum on the number of implementation
  // ports this port can connect to. A port is unbounded when the ~max_size~
  // argument in the constructor is specified as ~UVM_UNBOUNDED_CONNECTIONS~.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.8
  function bit is_unbounded ();
    return (m_max_size ==  UVM_UNBOUNDED_CONNECTIONS);
  endfunction


  // Function -- NODOCS -- is_port

  // @uvm-ieee 1800.2-2017 auto 5.5.2.11
  function bit is_port ();
    return m_port_type == UVM_PORT;
  endfunction

  // Function -- NODOCS -- is_export

  // @uvm-ieee 1800.2-2017 auto 5.5.2.11
  function bit is_export ();
    return m_port_type == UVM_EXPORT;
  endfunction

  // Function -- NODOCS -- is_imp
  //
  // Returns 1 if this port is of the type given by the method name,
  // 0 otherwise.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.11
  function bit is_imp ();
    return m_port_type == UVM_IMPLEMENTATION;
  endfunction


  // Function -- NODOCS -- size
  //
  // Gets the number of implementation ports connected to this port. The value
  // is not valid before the end_of_elaboration phase, as port connections have
  // not yet been resolved.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.12
  function int size ();
    return m_imp_list.num();
  endfunction


  function void set_if (int index=0);
    m_if = get_if(index);
    if (m_if != null)
      m_def_index = index;
  endfunction

  function int m_get_if_mask();
    return m_if_mask;
  endfunction


  // Function -- NODOCS -- set_default_index
  // 
  // Sets the default implementation port to use when calling an interface
  // method. This method should only be called on UVM_EXPORT types. The value
  // must not be set before the end_of_elaboration phase, when port connections
  // have not yet been resolved.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.13
  function void set_default_index (int index);
    m_def_index = index;
  endfunction


  // Function -- NODOCS -- connect
  //
  // Connects this port to the given ~provider~ port. The ports must be 
  // compatible in the following ways
  //
  // - Their type parameters must match
  //
  // - The ~provider~'s interface type (blocking, non-blocking, analysis, etc.)
  //   must be compatible. Each port has an interface mask that encodes the
  //   interface(s) it supports. If the bitwise AND of these masks is equal to
  //   the this port's mask, the requirement is met and the ports are
  //   compatible. For example, a uvm_blocking_put_port #(T) is compatible with
  //   a uvm_put_export #(T) and uvm_blocking_put_imp #(T) because the export
  //   and imp provide the interface required by the uvm_blocking_put_port.
  // 
  // - Ports of type <UVM_EXPORT> can only connect to other exports or imps.
  //
  // - Ports of type <UVM_IMPLEMENTATION> cannot be connected, as they are
  //   bound to the component that implements the interface at time of
  //   construction.
  //
  // In addition to type-compatibility checks, the relationship between this
  // port and the ~provider~ port will also be checked if the port's
  // ~check_connection_relationships~ configuration has been set. (See <new>
  // for more information.)
  //
  // Relationships, when enabled, are checked are as follows:
  //
  // - If this port is an UVM_PORT type, the ~provider~ can be a parent port,
  //   or a sibling export or implementation port.
  //
  // - If this port is a <UVM_EXPORT> type, the provider can be a child
  //   export or implementation port.
  //
  // If any relationship check is violated, a warning is issued.
  //
  // Note- the <uvm_component::connect_phase> method is related to but not the same
  // as this method. The component's ~connect~ method is a phase callback where
  // port's ~connect~ method calls are made.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.14
  virtual function void connect (this_type provider);
     uvm_root top;
     uvm_coreservice_t cs;
     cs = uvm_coreservice_t::get();
     top = cs.get_root();
    if (end_of_elaboration_ph.get_state() == UVM_PHASE_EXECUTING || // TBD tidy
        end_of_elaboration_ph.get_state() == UVM_PHASE_DONE ) begin
       m_comp.uvm_report_warning("Late Connection", 
         {"Attempt to connect ",this.get_full_name()," (of type ",this.get_type_name(),
          ") at or after end_of_elaboration phase.  Ignoring."});
       return;
     end

    if (provider == null) begin
      m_comp.uvm_report_error(s_connection_error_id,
                       "Cannot connect to null port handle", UVM_NONE);
      return;
    end
    
    if (provider == this) begin
      m_comp.uvm_report_error(s_connection_error_id,
                       "Cannot connect a port instance to itself", UVM_NONE);
      return;
    end

    if ((provider.m_if_mask & m_if_mask) != m_if_mask) begin
      m_comp.uvm_report_error(s_connection_error_id, 
        {provider.get_full_name(),
         " (of type ",provider.get_type_name(),
         ") does not provide the complete interface required of this port (type ",
         get_type_name(),")"}, UVM_NONE);
      return;
    end

    // IMP.connect(anything) is illegal
    if (is_imp()) begin
      m_comp.uvm_report_error(s_connection_error_id,
        $sformatf(
"Cannot call an imp port's connect method. An imp is connected only to the component passed in its constructor. (You attempted to bind this imp to %s)", provider.get_full_name()), UVM_NONE);
      return;
    end
  
    // EXPORT.connect(PORT) are illegal
    if (is_export() && provider.is_port()) begin
      m_comp.uvm_report_error(s_connection_error_id,
        $sformatf(
"Cannot connect exports to ports Try calling port.connect(export) instead. (You attempted to bind this export to %s).", provider.get_full_name()), UVM_NONE);
      return;
    end
  
    void'(m_check_relationship(provider));
  
    m_provided_by[provider.get_full_name()] = provider;
    provider.m_provided_to[get_full_name()] = this;
    
  endfunction


  // Function: debug_connected_to
  //
  // The ~debug_connected_to~ method outputs a visual text display of the
  // port/export/imp network to which this port connects (i.e., the port's
  // fanout).
  //
  // This method must not be called before the end_of_elaboration phase, as port
  // connections are not resolved until then.

  function void debug_connected_to (int level=0, int max_level=-1);
    int sz, num, curr_num;
    string s_sz;
    static string indent, save;
    this_type port;
  
    if (level <  0) level = 0;
    if (level == 0) begin save = ""; indent="  "; end
  
    if (max_level != -1 && level >= max_level)
      return;
  
    num = m_provided_by.num();
  
    if (m_provided_by.num() != 0) begin
      foreach (m_provided_by[nm]) begin
        curr_num++;
        port = m_provided_by[nm];
        save = {save, indent, "  | \n"};
        save = {save, indent, "  |_",nm," (",port.get_type_name(),")\n"};
        indent = (num > 1 && curr_num != num) ?  {indent,"  | "}:{indent, "    "};
        port.debug_connected_to(level+1, max_level);
        indent = indent.substr(0,indent.len()-4-1);
      end
    end
  
    if (level == 0) begin
      if (save != "")
        save = {"This port's fanout network:\n\n  ",
               get_full_name()," (",get_type_name(),")\n",save,"\n"};
      if (m_imp_list.num() == 0) begin
	 uvm_root top;
	 uvm_coreservice_t cs;
	 cs = uvm_coreservice_t::get();
	 top = cs.get_root();
        if (end_of_elaboration_ph.get_state() == UVM_PHASE_EXECUTING ||
            end_of_elaboration_ph.get_state() == UVM_PHASE_DONE )  // TBD tidy
           save = {save,"  Connected implementations: none\n"};
        else
           save = {save,
                 "  Connected implementations: not resolved until end-of-elab\n"};
      end
      else begin
        save = {save,"  Resolved implementation list:\n"};
        foreach (m_imp_list[nm]) begin
          port = m_imp_list[nm];
          s_sz.itoa(sz);
          save = {save, indent, s_sz, ": ",nm," (",port.get_type_name(),")\n"};
          sz++;
        end
      end
      m_comp.uvm_report_info("debug_connected_to", save);
    end
  endfunction
  

  // Function: debug_provided_to
  //
  // The ~debug_provided_to~ method outputs a visual display of the port/export
  // network that ultimately connect to this port (i.e., the port's fanin).
  //
  // This method must not be called before the end_of_elaboration phase, as port
  // connections are not resolved until then.

  function void debug_provided_to  (int level=0, int max_level=-1);
    string nm;
    int num,curr_num;
    this_type port;
    static string indent, save;
  
    if (level <  0) level = 0; 
    if (level == 0) begin save = ""; indent = "  "; end

    if (max_level != -1 && level > max_level)
      return;
  
    num = m_provided_to.num();
  
    if (num != 0) begin
      foreach (m_provided_to[nm]) begin
        curr_num++;
        port = m_provided_to[nm];
        save = {save, indent, "  | \n"};
        save = {save, indent, "  |_",nm," (",port.get_type_name(),")\n"};
        indent = (num > 1 && curr_num != num) ?  {indent,"  | "}:{indent, "    "};
        port.debug_provided_to(level+1, max_level);
        indent = indent.substr(0,indent.len()-4-1);
      end
    end

    if (level == 0) begin
      if (save != "")
        save = {"This port's fanin network:\n\n  ",
               get_full_name()," (",get_type_name(),")\n",save,"\n"};
      if (m_provided_to.num() == 0)
        save = {save,indent,"This port has not been bound\n"};
      m_comp.uvm_report_info("debug_provided_to", save);
    end
  
  endfunction


  // get_connected_to
  // ----------------

  // @uvm-ieee 1800.2-2017 auto 5.5.2.9
  function void get_connected_to (ref uvm_port_base #(IF) list[string]);
    this_type port;
    list.delete();
    foreach (m_provided_by[name]) begin
      port = m_provided_by[name];
      list[name] = port;
    end
  endfunction


  // get_provided_to
  // ---------------

  // @uvm-ieee 1800.2-2017 auto 5.5.2.10
  function void get_provided_to (ref uvm_port_base #(IF) list[string]);
    this_type port;
    list.delete();
    foreach (m_provided_to[name]) begin
      port = m_provided_to[name];
      list[name] = port;
    end
  endfunction


  // m_check_relationship
  // --------------------

  local function bit  m_check_relationship (this_type provider);  
    string s;
    this_type from;
    uvm_component from_parent;
    uvm_component to_parent;
    uvm_component from_gparent;
    uvm_component to_gparent;
  
    // Checks that the connection is between ports that are hierarchically
    // adjacent (up or down one level max, or are siblings),
    // and check for legal direction, requirer.connect(provider).

    // if we're an analysis port, allow connection to anywhere
    if (get_type_name() == "uvm_analysis_port")
      return 1;
    
    from         = this;
    from_parent  = get_parent();
    to_parent    = provider.get_parent();
  
    // skip check if we have a parentless port
    if (from_parent == null || to_parent == null)
      return 1;
  
    from_gparent = from_parent.get_parent();
    to_gparent   = to_parent.get_parent();
  
    // Connecting port-to-port: CHILD.port.connect(PARENT.port)
    //
    if (from.is_port() && provider.is_port() && from_gparent != to_parent) begin
      s = {provider.get_full_name(),
           " (of type ",provider.get_type_name(),
           ") is not up one level of hierarchy from this port. ",
           "A port-to-port connection takes the form ",
           "child_component.child_port.connect(parent_port)"};
      m_comp.uvm_report_warning(s_connection_warning_id, s, UVM_NONE);
      return 0;
    end    
      
    // Connecting port-to-export: SIBLING.port.connect(SIBLING.export)
    // Connecting port-to-imp:    SIBLING.port.connect(SIBLING.imp)
    //
    else if (from.is_port() && (provider.is_export() || provider.is_imp()) &&
             from_gparent != to_gparent) begin
        s = {provider.get_full_name(),
           " (of type ",provider.get_type_name(),
           ") is not at the same level of hierarchy as this port. ",
           "A port-to-export connection takes the form ",
           "component1.port.connect(component2.export)"};
      m_comp.uvm_report_warning(s_connection_warning_id, s, UVM_NONE);
      return 0;
    end
  
    // Connecting export-to-export: PARENT.export.connect(CHILD.export)
    // Connecting export-to-imp:    PARENT.export.connect(CHILD.imp)
    //
    else if (from.is_export() && (provider.is_export() || provider.is_imp()) &&
             from_parent != to_gparent) begin
      s = {provider.get_full_name(),
           " (of type ",provider.get_type_name(),
           ") is not down one level of hierarchy from this export. ",
           "An export-to-export or export-to-imp connection takes the form ",
           "parent_export.connect(child_component.child_export)"};
      m_comp.uvm_report_warning(s_connection_warning_id, s, UVM_NONE);
      return 0;
    end

    return 1;
  endfunction


  // m_add_list
  //
  // Internal method.

  local function void m_add_list           (this_type provider);
    string sz;
    this_type imp;

    for (int i = 0; i < provider.size(); i++) begin
      imp = provider.get_if(i);
      if (!m_imp_list.exists(imp.get_full_name()))
        m_imp_list[imp.get_full_name()] = imp;
    end

  endfunction


  // Function -- NODOCS -- resolve_bindings
  //
  // This callback is called just before entering the end_of_elaboration phase.
  // It recurses through each port's fanout to determine all the imp 
  // destinations. It then checks against the required min and max connections.
  // After resolution, <size> returns a valid value and <get_if>
  // can be used to access a particular imp.
  //
  // This method is automatically called just before the start of the
  // end_of_elaboration phase. Users should not need to call it directly.

  // @uvm-ieee 1800.2-2017 auto 5.5.2.15
  virtual function void resolve_bindings();
    if (m_resolved) // don't repeat ourselves
     return;

    if (is_imp()) begin
      m_imp_list[get_full_name()] = this;
    end
    else begin
      foreach (m_provided_by[nm]) begin
        this_type port;
        port = m_provided_by[nm];
        port.resolve_bindings();
        m_add_list(port);
      end
    end
  
    m_resolved = 1;
  
    if (size() < min_size() ) begin
      m_comp.uvm_report_error(s_connection_error_id, 
        $sformatf("connection count of %0d does not meet required minimum of %0d",
        size(), min_size()), UVM_NONE);
    end
  
    if (max_size() != UVM_UNBOUNDED_CONNECTIONS && size() > max_size() ) begin
      m_comp.uvm_report_error(s_connection_error_id, 
        $sformatf("connection count of %0d exceeds maximum of %0d",
        size(), max_size()), UVM_NONE);
    end

    if (size())
      set_if(0);
  
  endfunction
  

  // Function -- NODOCS -- get_if
  //
  // Returns the implementation (imp) port at the given index from the array of
  // imps this port is connected to. Use <size> to get the valid range for index.
  // This method can only be called at the end_of_elaboration phase or after, as
  // port connections are not resolved before then.

  function uvm_port_base #(IF) get_if(int index=0);
    string s;
    if (size()==0) begin
      m_comp.uvm_report_warning("get_if",
        "Port size is zero; cannot get interface at any index", UVM_NONE);
      return null;
    end
    if (index < 0 || index >= size()) begin
      $sformat(s, "Index %0d out of range [0,%0d]", index, size()-1);
      m_comp.uvm_report_warning(s_connection_error_id, s, UVM_NONE);
      return null;
    end
    foreach (m_imp_list[nm]) begin
      if (index == 0)
        return m_imp_list[nm];
      index--;
    end
  endfunction

endclass
