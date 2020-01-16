//
//-----------------------------------------------------------------------------
// Copyright 2007-2014 Mentor Graphics Corporation
// Copyright 2015 Analog Devices, Inc.
// Copyright 2014 Intel Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2013-2018 NVIDIA Corporation
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
typedef class uvm_simple_lock_dap;
typedef class uvm_text_tr_stream;
   
   

//------------------------------------------------------------------------------
//
// CLASS: uvm_text_tr_database
//
// The ~uvm_text_tr_database~ is the default implementation for the
// <uvm_tr_database>.  It provides the ability to store recording information
// into a textual log file.
//
//
   
class uvm_text_tr_database extends uvm_tr_database;

   // Variable- m_filename_dap
   // Data Access Protected Filename
   local uvm_simple_lock_dap#(string) m_filename_dap;

   // Variable- m_file
   UVM_FILE m_file;

   `uvm_object_utils(uvm_text_tr_database)

   // Function: new
   // Constructor
   //
   // Parameters:
   // name - Instance name
   function new(string name="unnamed-uvm_text_tr_database");
      super.new(name);

      m_filename_dap = new("filename_dap");
      m_filename_dap.set("tr_db.log");
   endfunction : new

   // Group: Implementation Agnostic API
   
   // Function: do_open_db
   // Open the backend connection to the database.
   //
   // Text-Backend implementation of <uvm_tr_database::open_db>.
   //
   // The text-backend will open a text file to dump all records in to.  The name
   // of this text file is controlled via <set_file_name>.
   //
   // This will also lock the ~file_name~, so that it cannot be
   // modified while the connection is open.
   protected virtual function bit do_open_db();
      if (m_file == 0) begin
         m_file = $fopen(m_filename_dap.get(), "a+");
         if (m_file != 0)
           m_filename_dap.lock();
      end
      return (m_file != 0);
   endfunction : do_open_db
   
   // Function: do_close_db
   // Close the backend connection to the database.
   //
   // Text-Backend implementation of <uvm_tr_database::close_db>.
   //
   // The text-backend will close the text file used to dump all records in to,
   // if it is currently opened.
   //
   // This unlocks the ~file_name~, allowing it to be modified again.
   protected virtual function bit do_close_db();
      if (m_file != 0) begin
         fork // Needed because $fclose is a task
            $fclose(m_file);
         join_none
         m_filename_dap.unlock();
      end
      return 1;
   endfunction : do_close_db
   
   // Function: do_open_stream
   // Provides a reference to a ~stream~ within the
   // database.
   //
   // Text-Backend implementation of <uvm_tr_database::open_stream>
   protected virtual function uvm_tr_stream do_open_stream(string name,
                                                           string scope,
                                                           string type_name);
      uvm_text_tr_stream m_stream = uvm_text_tr_stream::type_id::create(name);
      return m_stream;
   endfunction : do_open_stream

   // Function: do_establish_link
   // Establishes a ~link~ between two elements in the database
   //
   // Text-Backend implementation of <uvm_tr_database::establish_link>.
   protected virtual function void do_establish_link(uvm_link_base link);
      uvm_recorder r_lhs, r_rhs;
      uvm_object lhs = link.get_lhs();
      uvm_object rhs = link.get_rhs();
      
      void'($cast(r_lhs, lhs));
      void'($cast(r_rhs, rhs));
      
      if ((r_lhs == null) ||
          (r_rhs == null))
        return;
      else begin
         uvm_parent_child_link pc_link;
         uvm_related_link re_link;
         if ($cast(pc_link, link)) begin
            $fdisplay(m_file,"  LINK @%0t {TXH1:%0d TXH2:%0d RELATION=%0s}",
                      $time,
                      r_lhs.get_handle(),
                      r_rhs.get_handle(),
                      "child");
            
         end
         else if ($cast(re_link, link)) begin
            $fdisplay(m_file,"  LINK @%0t {TXH1:%0d TXH2:%0d RELATION=%0s}",
                      $time,
                         r_lhs.get_handle(),
                      r_rhs.get_handle(),
                      "");
            
         end
      end
   endfunction : do_establish_link

   // Group: Implementation Specific API
   
   // Function: set_file_name
   // Sets the file name which will be used for output.
   //
   // The ~set_file_name~ method can only be called prior to ~open_db~.
   //
   // By default, the database will use a file named "tr_db.log".
   function void set_file_name(string filename);
      if (filename == "") begin
        `uvm_warning("UVM/TXT_DB/EMPTY_NAME",
                     "Ignoring attempt to set file name to ''!")
         return;
      end

      if (!m_filename_dap.try_set(filename)) begin
         `uvm_warning("UVM/TXT_DB/SET_AFTER_OPEN",
                      "Ignoring attempt to change file name after opening the db!")
         return;
      end
   endfunction : set_file_name

   
endclass : uvm_text_tr_database
