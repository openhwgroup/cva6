// 
//------------------------------------------------------------------------------
// Copyright 2007-2009 Mentor Graphics Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013-2015 NVIDIA Corporation
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

// Class -- NODOCS -- uvm_set_get_dap_base
// Provides the 'set' and 'get' interface for Data Access Policies (DAPs)
//
// The 'Set/Get' base class simply provides a common interface for
// the various DAPs to implement.  This provides a mechanism for
// consistent implementations of similar DAPs.
//

virtual class uvm_set_get_dap_base#(type T=int) extends uvm_object;

   // Used for self references
   typedef uvm_set_get_dap_base#(T) this_type;

   // Function -- NODOCS -- new
   // Constructor
   function new(string name="unnamed-uvm_set_get_dap_base#(T)");
      super.new(name);
   endfunction : new

   // Group -- NODOCS -- Set/Get Interface
   //
   // All implementations of the ~uvm_set_get_dap_base~ class must
   // provide an implementation of the four basic "Set and Get"
   // accessors.
   //

   // Function -- NODOCS -- set
   // Sets the value contained within the resource.
   //
   // Depending on the DAP policies, an error may be reported if
   // it is illegal to 'set' the value at this time.
   pure virtual function void set(T value);

   // Function -- NODOCS -- try_set
   // Attempts to set the value contained within the resource.
   //
   // If the DAP policies forbid setting at this time, then
   // the method will return 0, however no errors will be
   // reported.  Otherwise, the method will return 1, and
   // will be treated like a standard <set> call.
   pure virtual function bit try_set(T value);
   
   // Function -- NODOCS -- get
   // Retrieves the value contained within the resource.
   //
   // Depending on the DAP policies, an error may be reported
   // if it is illegal to 'get' the value at this time.
   pure virtual function T get();

   // Function -- NODOCS -- try_get
   // Attempts to retrieve the value contained within the resource.
   //
   // If the DAP policies forbid retrieving at this time, then
   // the method will return 0, however no errors will be
   // reported.  Otherwise, the method will return 1, and will
   // be treated like a standard <get> call.
   pure virtual function bit try_get(output T value);

endclass : uvm_set_get_dap_base
