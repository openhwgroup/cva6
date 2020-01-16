//
//-----------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2014 Intel Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013-2015 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
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

//------------------------------------------------------------------------------
// File -- NODOCS -- Transaction Recording Databases
//
// The UVM "Transaction Recording Database" classes are an abstract representation
// of the backend tool which is recording information for the user.  Usually this
// tool would be dumping information such that it can be viewed with the ~waves~ 
// of the DUT.
//

typedef class uvm_recorder;
typedef class uvm_tr_stream;
typedef class uvm_link_base;
   
   
//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_tr_database
//
// The ~uvm_tr_database~ class is intended to hide the underlying database implementation
// from the end user, as these details are often vendor or tool-specific.
//
// The ~uvm_tr_database~ class is pure virtual, and must be extended with an
// implementation.  A default text-based implementation is provided via the
// <uvm_text_tr_database> class.
//

// @uvm-ieee 1800.2-2017 auto 7.1.1
virtual class uvm_tr_database extends uvm_object;

   // Variable- m_is_opened
   // Tracks the opened state of the database
   local bit m_is_opened;

   // Variable- m_streams
   // Used for tracking streams which are between the open and closed states
   local bit m_streams[uvm_tr_stream];
   

   // @uvm-ieee 1800.2-2017 auto 7.1.2
   function new(string name="unnamed-uvm_tr_database");
      super.new(name);
   endfunction : new

   // Group -- NODOCS -- Database API
   

   // @uvm-ieee 1800.2-2017 auto 7.1.3.1
   function bit open_db();
      if (!m_is_opened)
        m_is_opened = do_open_db();
      return m_is_opened;
   endfunction : open_db


   // @uvm-ieee 1800.2-2017 auto 7.1.3.2
   function bit close_db();
      if (m_is_opened) begin
         if (do_close_db())
           m_is_opened = 0;
      end
      return (m_is_opened == 0);
   endfunction : close_db


   // @uvm-ieee 1800.2-2017 auto 7.1.3.3
   function bit is_open();
      return m_is_opened;
   endfunction : is_open

   // Group -- NODOCS -- Stream API
   

   // @uvm-ieee 1800.2-2017 auto 7.1.4.1
   function uvm_tr_stream open_stream(string name,
                                      string scope="",
                                      string type_name="");
      if (!open_db()) begin
         return null;
      end
      else begin
         process p = process::self();
         string s;

         if (p != null)
           s = p.get_randstate();

         open_stream = do_open_stream(name, scope, type_name);


         if (open_stream != null) begin
            m_streams[open_stream] = 1;
            open_stream.m_do_open(this, scope, type_name);
         end
         
         if (p != null)
           p.set_randstate(s);

      end
   endfunction : open_stream

   // Function- m_free_stream
   // Removes stream from the internal array
   function void m_free_stream(uvm_tr_stream stream);
      if (m_streams.exists(stream))
        m_streams.delete(stream);
   endfunction : m_free_stream
   

   // @uvm-ieee 1800.2-2017 auto 7.1.4.2
   function unsigned get_streams(ref uvm_tr_stream q[$]);
      // Clear out the queue first...
      q.delete();
      // Then fill in the values
      foreach (m_streams[idx])
        q.push_back(idx);
      // Finally, return the size of the queue
      return q.size();
   endfunction : get_streams
   
   // Group -- NODOCS -- Link API
   

   // @uvm-ieee 1800.2-2017 auto 7.1.5
   function void establish_link(uvm_link_base link);
      uvm_tr_stream s_lhs, s_rhs;
      uvm_recorder r_lhs, r_rhs;
      uvm_object lhs = link.get_lhs();
      uvm_object rhs = link.get_rhs();
      uvm_tr_database db;

      if (lhs == null) begin
         `uvm_warning("UVM/TR_DB/BAD_LINK",
                      "left hand side '<null>' is not supported in links for 'uvm_tr_database'")
         return;
      end
      if (rhs == null) begin
         `uvm_warning("UVM/TR_DB/BAD_LINK",
                      "right hand side '<null>' is not supported in links for 'uvm_tr_database'")
         return;
      end
      
      if (!$cast(s_lhs, lhs) && 
          !$cast(r_lhs, lhs)) begin
         `uvm_warning("UVM/TR_DB/BAD_LINK",
                      $sformatf("left hand side of type '%s' not supported in links for 'uvm_tr_database'",
                                lhs.get_type_name()))
         return;
      end
      if (!$cast(s_rhs, rhs) && 
          !$cast(r_rhs, rhs)) begin
         `uvm_warning("UVM/TR_DB/BAD_LINK",
                      $sformatf("right hand side of type '%s' not supported in links for 'uvm_record_datbasae'",
                                rhs.get_type_name()))
         return;
      end
      
      if (r_lhs != null) begin
         s_lhs = r_lhs.get_stream();
      end
      if (r_rhs != null) begin
         s_rhs = r_rhs.get_stream();
      end

      if ((s_lhs != null) && (s_lhs.get_db() != this)) begin
         db = s_lhs.get_db();
         `uvm_warning("UVM/TR_DB/BAD_LINK",
                      $sformatf("attempt to link stream from '%s' into '%s'",
                                db.get_name(), this.get_name()))
         return;
      end
      if ((s_rhs != null) && (s_rhs.get_db() != this)) begin
         db = s_rhs.get_db();
         `uvm_warning("UVM/TR_DB/BAD_LINK",
                      $sformatf("attempt to link stream from '%s' into '%s'",
                                db.get_name(), this.get_name()))
         return;
      end

      do_establish_link(link);
   endfunction : establish_link
      
   // Group -- NODOCS -- Implementation Agnostic API
   //


   // @uvm-ieee 1800.2-2017 auto 7.1.6.1
   pure virtual protected function bit do_open_db();


   // @uvm-ieee 1800.2-2017 auto 7.1.6.2
   pure virtual protected function bit do_close_db();


   // @uvm-ieee 1800.2-2017 auto 7.1.6.3
   pure virtual protected function uvm_tr_stream do_open_stream(string name,
                                                                string scope,
                                                                string type_name);


   // @uvm-ieee 1800.2-2017 auto 7.1.6.4
   pure virtual protected function void do_establish_link(uvm_link_base link);

endclass : uvm_tr_database

