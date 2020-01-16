//
//-----------------------------------------------------------------------------
// Copyright 2007-2009 Mentor Graphics Corporation
// Copyright 2014 Intel Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013-2018 NVIDIA Corporation
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

// File -- NODOCS -- UVM Links
//
// The <uvm_link_base> class, and its extensions, are provided as a mechanism
// to allow for compile-time safety when trying to establish links between
// records within a <uvm_tr_database>.
//
// 


// @uvm-ieee 1800.2-2017 auto 7.3.1.1
virtual class uvm_link_base extends uvm_object;


   // @uvm-ieee 1800.2-2017 auto 7.3.1.2
   function new(string name="unnamed-uvm_link_base");
      super.new(name);
   endfunction : new

   // Group -- NODOCS --  Accessors


   // @uvm-ieee 1800.2-2017 auto 7.3.1.3.2
   function void set_lhs(uvm_object lhs);
      do_set_lhs(lhs);
   endfunction : set_lhs


   // @uvm-ieee 1800.2-2017 auto 7.3.1.3.1
   function uvm_object get_lhs();
      return do_get_lhs();
   endfunction : get_lhs


   // @uvm-ieee 1800.2-2017 auto 7.3.1.3.4
   function void set_rhs(uvm_object rhs);
      do_set_rhs(rhs);
   endfunction : set_rhs


   // @uvm-ieee 1800.2-2017 auto 7.3.1.3.3
   function uvm_object get_rhs();
      return do_get_rhs();
   endfunction : get_rhs


   // @uvm-ieee 1800.2-2017 auto 7.3.1.3.5
   function void set(uvm_object lhs, rhs);
      do_set_lhs(lhs);
      do_set_rhs(rhs);
   endfunction : set

   // Group -- NODOCS -- Implementation Callbacks


   // @uvm-ieee 1800.2-2017 auto 7.3.1.4.2
   pure virtual function void do_set_lhs(uvm_object lhs);


   // @uvm-ieee 1800.2-2017 auto 7.3.1.4.1
   pure virtual function uvm_object do_get_lhs();


   // @uvm-ieee 1800.2-2017 auto 7.3.1.4.4
   pure virtual function void do_set_rhs(uvm_object rhs);


   // @uvm-ieee 1800.2-2017 auto 7.3.1.4.3
   pure virtual function uvm_object do_get_rhs();

endclass : uvm_link_base

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_parent_child_link
//
// The ~uvm_parent_child_link~ is used to represent a Parent/Child relationship
// between two objects.
//

// @uvm-ieee 1800.2-2017 auto 7.3.2.1
class uvm_parent_child_link extends uvm_link_base;

   // Variable- m_lhs,m_rhs
   // Implementation details
   local uvm_object m_lhs;
   local uvm_object m_rhs;

   // Object utils
   `uvm_object_utils(uvm_parent_child_link)


   // @uvm-ieee 1800.2-2017 auto 7.3.2.2.1
   function new(string name="unnamed-uvm_parent_child_link");
      super.new(name);
   endfunction : new


   // @uvm-ieee 1800.2-2017 auto 7.3.2.2.2
   static function uvm_parent_child_link get_link(uvm_object lhs,
                                                  uvm_object rhs,
                                                  string name="pc_link");
      process p_;
      string s_;

      p_ = process::self();
      if (p_ != null)
	s_ = p_.get_randstate();
      
      get_link = new(name);

      if (p_ != null)
	p_.set_randstate(s_);
      
      get_link.set(lhs, rhs);
   endfunction : get_link
   
   // Group -- NODOCS -- Implementation Callbacks

   // Function -- NODOCS -- do_set_lhs
   // Sets the left-hand-side (Parent)
   //
   virtual function void do_set_lhs(uvm_object lhs);
      m_lhs = lhs;
   endfunction : do_set_lhs

   // Function -- NODOCS -- do_get_lhs
   // Retrieves the left-hand-side (Parent)
   //
   virtual function uvm_object do_get_lhs();
      return m_lhs;
   endfunction : do_get_lhs

   // Function -- NODOCS -- do_set_rhs
   // Sets the right-hand-side (Child)
   //
   virtual function void do_set_rhs(uvm_object rhs);
      m_rhs = rhs;
   endfunction : do_set_rhs

   // Function -- NODOCS -- do_get_rhs
   // Retrieves the right-hand-side (Child)
   //
   virtual function uvm_object do_get_rhs();
      return m_rhs;
   endfunction : do_get_rhs

endclass : uvm_parent_child_link

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_cause_effect_link
//
// The ~uvm_cause_effect_link~ is used to represent a Cause/Effect relationship
// between two objects.
//

// @uvm-ieee 1800.2-2017 auto 7.3.3.1
class uvm_cause_effect_link extends uvm_link_base;

   // Variable- m_lhs,m_rhs
   // Implementation details
   local uvm_object m_lhs;
   local uvm_object m_rhs;

   // Object utils
   `uvm_object_utils(uvm_cause_effect_link)


   // @uvm-ieee 1800.2-2017 auto 7.3.3.2.1
   function new(string name="unnamed-uvm_cause_effect_link");
      super.new(name);
   endfunction : new


   // @uvm-ieee 1800.2-2017 auto 7.3.3.2.2
   static function uvm_cause_effect_link get_link(uvm_object lhs,
                                                 uvm_object rhs,
                                                 string name="ce_link");
      process p_;
      string s_;
      p_ = process::self();
      if (p_ != null)
	s_ = p_.get_randstate();
      
      get_link = new(name);

      if (p_ != null)
	p_.set_randstate(s_);
      
      get_link.set(lhs, rhs);
   endfunction : get_link
   
   // Group -- NODOCS -- Implementation Callbacks

   // Function -- NODOCS -- do_set_lhs
   // Sets the left-hand-side (Cause)
   //
   virtual function void do_set_lhs(uvm_object lhs);
      m_lhs = lhs;
   endfunction : do_set_lhs

   // Function -- NODOCS -- do_get_lhs
   // Retrieves the left-hand-side (Cause)
   //
   virtual function uvm_object do_get_lhs();
      return m_lhs;
   endfunction : do_get_lhs

   // Function -- NODOCS -- do_set_rhs
   // Sets the right-hand-side (Effect)
   //
   virtual function void do_set_rhs(uvm_object rhs);
      m_rhs = rhs;
   endfunction : do_set_rhs

   // Function -- NODOCS -- do_get_rhs
   // Retrieves the right-hand-side (Effect)
   //
   virtual function uvm_object do_get_rhs();
      return m_rhs;
   endfunction : do_get_rhs

endclass : uvm_cause_effect_link

//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_related_link
//
// The ~uvm_related_link~ is used to represent a generic "is related" link
// between two objects.
//

// @uvm-ieee 1800.2-2017 auto 7.3.4.1
class uvm_related_link extends uvm_link_base;

   // Variable- m_lhs,m_rhs
   // Implementation details
   local uvm_object m_lhs;
   local uvm_object m_rhs;

   // Object utils
   `uvm_object_utils(uvm_related_link)


   // @uvm-ieee 1800.2-2017 auto 7.3.4.2.1
   function new(string name="unnamed-uvm_related_link");
      super.new(name);
   endfunction : new


   // @uvm-ieee 1800.2-2017 auto 7.3.4.2.2
   static function uvm_related_link get_link(uvm_object lhs,
                                                 uvm_object rhs,
                                                 string name="ce_link");
      process p_;
      string s_;
      p_ = process::self();
      if (p_ != null)
	s_ = p_.get_randstate();
      
      get_link = new(name);

      if (p_ != null)
	p_.set_randstate(s_);
      
      get_link.set(lhs, rhs);
   endfunction : get_link
   
   // Group -- NODOCS -- Implementation Callbacks

   // Function -- NODOCS -- do_set_lhs
   // Sets the left-hand-side
   //
   virtual function void do_set_lhs(uvm_object lhs);
      m_lhs = lhs;
   endfunction : do_set_lhs

   // Function -- NODOCS -- do_get_lhs
   // Retrieves the left-hand-side
   //
   virtual function uvm_object do_get_lhs();
      return m_lhs;
   endfunction : do_get_lhs

   // Function -- NODOCS -- do_set_rhs
   // Sets the right-hand-side
   //
   virtual function void do_set_rhs(uvm_object rhs);
      m_rhs = rhs;
   endfunction : do_set_rhs

   // Function -- NODOCS -- do_get_rhs
   // Retrieves the right-hand-side
   //
   virtual function uvm_object do_get_rhs();
      return m_rhs;
   endfunction : do_get_rhs

endclass : uvm_related_link
