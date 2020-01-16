//----------------------------------------------------------------------
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2014-2018 NVIDIA Corporation
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

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_visitor #(NODE)
//
// The uvm_visitor class provides an abstract base class for a visitor. The visitor 
// visits instances of type NODE. For general information regarding the visitor pattern
// see http://en.wikipedia.org/wiki/Visitor_pattern
// 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.5.1.1
virtual class uvm_visitor#(type NODE=uvm_component) extends uvm_object;
  function new (string name = "");
    super.new(name);
  endfunction 

  // Function -- NODOCS -- begin_v
  //
  // This method will be invoked by the visitor before the first NODE is visited
  
  // @uvm-ieee 1800.2-2017 auto F.5.1.2.1
  virtual function void begin_v(); endfunction
  
  // Function -- NODOCS -- end_v
  //
  // This method will be invoked by the visitor after the last NODE is visited
    
  // @uvm-ieee 1800.2-2017 auto F.5.1.2.2
  virtual function void end_v(); endfunction


  // @uvm-ieee 1800.2-2017 auto F.5.1.2.3
  pure virtual function void visit(NODE node);
endclass

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_structure_proxy #(STRUCTURE)
//
// The uvm_structure_proxy is a wrapper and provides a set of elements 
// of the STRUCTURE to the caller on demand. This is to decouple the retrieval of 
// the STRUCTUREs subelements from the actual function being invoked on STRUCTURE
// 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.5.2.1
virtual class uvm_structure_proxy#(type STRUCTURE=uvm_component) extends uvm_object;
  // @uvm-ieee 1800.2-2017 auto F.5.2.2.1
  function new (string name = "");
    super.new(name);
  endfunction     

  // Function -- NODOCS -- get_immediate_children
  //
  // This method will be return in ~children~ a set of the direct subelements of ~s~
    
  // @uvm-ieee 1800.2-2017 auto F.5.2.2.2
  pure virtual function void get_immediate_children(STRUCTURE s, ref STRUCTURE children[$]);
endclass    

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_visitor_adapter #(STRUCTURE,uvm_visitor#(STRUCTURE))
//
// The visitor adaptor traverses all nodes of the STRUCTURE and will invoke visitor.visit() on every node.
// 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.5.3.1
virtual class uvm_visitor_adapter#(type STRUCTURE=uvm_component,VISITOR=uvm_visitor#(STRUCTURE)) extends uvm_object;
  // Function -- NODOCS -- accept()
  //
  // Calling this function will traverse through ~s~ (and every subnode of ~s~). For each node found 
  // ~v~.visit(node) will be invoked. The children of ~s~ are recursively determined 
  // by invoking ~p~.get_immediate_children().~invoke_begin_end~ determines whether the visitors begin/end functions 
  // should be invoked prior to traversal.
  
  // @uvm-ieee 1800.2-2017 auto F.5.3.2.2
  pure virtual function void accept(STRUCTURE s, VISITOR v,uvm_structure_proxy#(STRUCTURE) p, bit invoke_begin_end=1);

  // @uvm-ieee 1800.2-2017 auto F.5.3.2.1
  function new (string name = "");
    super.new(name);
  endfunction 
endclass

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_top_down_visitor_adapter
//
// This uvm_top_down_visitor_adapter traverses the STRUCTURE ~s~ (and will invoke the visitor) in a hierarchical fashion.
// During traversal ~s~ will be visited before all subnodes of ~s~ will be visited.
// 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.5.4.1
class uvm_top_down_visitor_adapter#(type STRUCTURE=uvm_component,VISITOR=uvm_visitor#(STRUCTURE)) extends 
  uvm_visitor_adapter#(STRUCTURE,VISITOR);

  // @uvm-ieee 1800.2-2017 auto F.5.4.2
  function new (string name = "");
    super.new(name);
  endfunction         

  virtual function void accept(STRUCTURE s, VISITOR v,uvm_structure_proxy#(STRUCTURE) p, bit invoke_begin_end=1);
    STRUCTURE c[$];

    if(invoke_begin_end)
      v.begin_v();

    v.visit(s);
    p.get_immediate_children(s, c);

    foreach(c[idx])
      accept(c[idx],v,p,0);

    if(invoke_begin_end)
      v.end_v();

  endfunction
endclass

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_bottom_up_visitor_adapter
//
// This uvm_bottom_up_visitor_adapter traverses the STRUCTURE ~s~ (and will invoke the visitor) in a hierarchical fashion.
// During traversal all children of node ~s~ will be visited ~s~ will be visited.
// 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.5.5.1
class uvm_bottom_up_visitor_adapter#(type STRUCTURE=uvm_component,VISITOR=uvm_visitor#(STRUCTURE)) extends 
  uvm_visitor_adapter#(STRUCTURE,VISITOR);

  // @uvm-ieee 1800.2-2017 auto F.5.5.2
  function new (string name = "");
    super.new(name);
  endfunction         

  virtual function void accept(STRUCTURE s, VISITOR v,uvm_structure_proxy#(STRUCTURE) p, bit invoke_begin_end=1);
    STRUCTURE c[$];

    if(invoke_begin_end)
      v.begin_v();

    p.get_immediate_children(s, c);
    foreach(c[idx])
      accept(c[idx],v,p,0);

    v.visit(s);

    if(invoke_begin_end)
      v.end_v();

  endfunction
endclass

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_by_level_visitor_adapter
//
// This uvm_by_level_visitor_adapter traverses the STRUCTURE ~s~ (and will invoke the visitor) in a hierarchical fashion.
// During traversal will visit all direct children of ~s~ before all grand-children are visited. 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.5.6.1
class uvm_by_level_visitor_adapter#(type STRUCTURE=uvm_component,VISITOR=uvm_visitor#(STRUCTURE)) extends 
  uvm_visitor_adapter#(STRUCTURE,VISITOR);

  // @uvm-ieee 1800.2-2017 auto F.5.6.2
  function new (string name = "");
    super.new(name);
  endfunction         

  virtual function void accept(STRUCTURE s, VISITOR v,uvm_structure_proxy#(STRUCTURE) p, bit invoke_begin_end=1);
    STRUCTURE c[$];
    c.push_back(s);

    if(invoke_begin_end)
      v.begin_v();

    while(c.size() > 0) begin
      STRUCTURE q[$];
      foreach(c[idx]) begin
        STRUCTURE t[$]; 

        v.visit(c[idx]);
        p.get_immediate_children(c[idx], t);
        q = {q,t};
      end 
      c=q;
    end 

    if(invoke_begin_end)
      v.end_v();
  endfunction
endclass

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_component_proxy
//
// The class is providing the proxy to extract the direct subcomponents of ~s~ 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto F.5.7.1
class uvm_component_proxy extends uvm_structure_proxy#(uvm_component);
  virtual function void get_immediate_children(STRUCTURE s, ref STRUCTURE children[$]);   
    s.get_children(children);   
  endfunction

  // @uvm-ieee 1800.2-2017 auto F.5.7.2
  function new (string name = "");
    super.new(name);
  endfunction 
endclass


//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_component_name_check_visitor 
//
// This specialized visitor analyze the naming of the current component. The established rule set
// ensures that a component.get_full_name() is parsable, unique, printable to order to avoid any ambiguities 
// when messages are being emitted.
// 
// ruleset a legal name is composed of
// - allowed charset "A-z:_0-9[](){}-: "
// - whitespace-as-is, no-balancing delimiter semantic, no escape sequences
// - path delimiter not allowed anywhere in the name
//   
// the check is coded here as a function to complete it in a single function call
// otherwise save/restore issues with the used dpi could occur
//------------------------------------------------------------------------------

  
class uvm_component_name_check_visitor extends uvm_visitor#(uvm_component);
  local uvm_root _root;

  // Function -- NODOCS -- get_name_constraint
  //
  // This method should return a regex for what is being considered a valid/good component name.
  // The visitor will check all component names using this regex and report failing names
    
  virtual function string get_name_constraint();
    return "/^[][[:alnum:](){}_:-]([][[:alnum:](){} _:-]*[][[:alnum:](){}_:-])?$/";
  endfunction

  virtual function void visit(NODE node);
    // dont check the root component
    if(_root != node) begin
      if ( ! uvm_is_match( get_name_constraint(), node.get_name() ) ) begin
        `uvm_warning("UVM/COMP/NAME",$sformatf("the name \"%s\" of the component \"%s\" violates the uvm component name constraints",node.get_name(),node.get_full_name()))
      end
    end
  endfunction 

  function new (string name = "");
    super.new(name);
  endfunction 

  virtual function void begin_v(); 
    uvm_coreservice_t cs = uvm_coreservice_t::get();

    _root =  cs.get_root();

`ifdef UVM_NO_DPI
    `uvm_info("UVM/COMP/NAMECHECK","This implementation of the component name checks requires DPI to be enabled",UVM_NONE)
`endif
  endfunction

endclass    
