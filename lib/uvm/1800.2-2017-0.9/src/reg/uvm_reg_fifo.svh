//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2014-2018 NVIDIA Corporation
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//


//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_reg_fifo
//
// This special register models a DUT FIFO accessed via write/read,
// where writes push to the FIFO and reads pop from it.
//
// Backdoor access is not enabled, as it is not yet possible to force
// complete FIFO state, i.e. the write and read indexes used to access
// the FIFO data.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.8.1
class uvm_reg_fifo extends uvm_reg;

    local uvm_reg_field value;
    local int m_set_cnt;
    local int unsigned m_size;

    // Variable -- NODOCS -- fifo
    //
    // The abstract representation of the FIFO. Constrained
    // to be no larger than the size parameter. It is public
    // to enable subtypes to add constraints on it and randomize.
    //
    rand uvm_reg_data_t fifo[$];

    constraint valid_fifo_size {
      fifo.size() <= m_size;
    }


    //----------------------
    // Group -- NODOCS -- Initialization
    //----------------------


    // @uvm-ieee 1800.2-2017 auto 18.8.3.1
    function new(string name = "reg_fifo",
                 int unsigned size,
                 int unsigned n_bits,
                 int has_cover);
       super.new(name,n_bits,has_cover);
       m_size = size;
    endfunction


    // Funtion: build
    //
    // Builds the abstract FIFO register object. Called by
    // the instantiating block, a <uvm_reg_block> subtype.
    //
    virtual function void build();
        value = uvm_reg_field::type_id::create("value");
        value.configure(this, get_n_bits(), 0, "RW", 0, 32'h0, 1, 0, 1);
    endfunction



    // @uvm-ieee 1800.2-2017 auto 18.8.3.2
    function void set_compare(uvm_check_e check=UVM_CHECK);
       value.set_compare(check);
    endfunction


    //---------------------
    // Group -- NODOCS -- Introspection
    //---------------------

    // Function -- NODOCS -- size
    //
    // The number of entries currently in the FIFO.
    //
    function int unsigned size();
      return fifo.size();
    endfunction


    // Function -- NODOCS -- capacity
    //
    // The maximum number of entries, or depth, of the FIFO.

    function int unsigned capacity();
      return m_size;
    endfunction


    //--------------
    // Group -- NODOCS -- Access
    //--------------

    //  Function -- NODOCS -- write
    // 
    //  Pushes the given value to the DUT FIFO. If auto-prediction is enabled,
    //  the written value is also pushed to the abstract FIFO before the
    //  call returns. If auto-prediction is not enabled (via 
    //  <uvm_reg_map::set_auto_predict>), the value is pushed to abstract
    //  FIFO only when the write operation is observed on the target bus.
    //  This mode requires using the <uvm_reg_predictor> class.
    //  If the write is via an <update()> operation, the abstract FIFO
    //  already contains the written value and is thus not affected by
    //  either prediction mode.


    //  Function -- NODOCS -- read
    //
    //  Reads the next value out of the DUT FIFO. If auto-prediction is
    //  enabled, the frontmost value in abstract FIFO is popped.



    // @uvm-ieee 1800.2-2017 auto 18.8.5.2
    virtual function void set(uvm_reg_data_t  value,
                              string          fname = "",
                              int             lineno = 0);
      // emulate write, with intention of update
      value &= ((1 << get_n_bits())-1);
      if (fifo.size() == m_size) begin
        return;
      end
      super.set(value,fname,lineno);
      m_set_cnt++;
      fifo.push_back(this.value.value);
    endfunction
    


    // @uvm-ieee 1800.2-2017 auto 18.8.5.7
    virtual task update(output uvm_status_e      status,
                        input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                        input  uvm_reg_map       map = null,
                        input  uvm_sequence_base parent = null,
                        input  int               prior = -1,
                        input  uvm_object        extension = null,
                        input  string            fname = "",
                        input  int               lineno = 0);
       uvm_reg_data_t upd;
       if (!m_set_cnt || fifo.size() == 0)
          return;
       m_update_in_progress = 1;
       for (int i=fifo.size()-m_set_cnt; m_set_cnt > 0; i++, m_set_cnt--) begin
         if (i >= 0) begin
            //uvm_reg_data_t val = get();
            //super.update(status,path,map,parent,prior,extension,fname,lineno);
            write(status,fifo[i],path,map,parent,prior,extension,fname,lineno);
         end
       end
       m_update_in_progress = 0;
    endtask


    // Function -- NODOCS -- mirror
    //
    // Reads the next value out of the DUT FIFO. If auto-prediction is
    // enabled, the frontmost value in abstract FIFO is popped. If 
    // the ~check~ argument is set and comparison is enabled with
    // <set_compare()>.



    // @uvm-ieee 1800.2-2017 auto 18.8.5.1
    virtual function uvm_reg_data_t get(string fname="", int lineno=0);
       //return fifo.pop_front();
       return fifo[0];
    endfunction


    // Function -- NODOCS -- do_predict
    //
    // Updates the abstract (mirror) FIFO based on <write()> and
    // <read()> operations.  When auto-prediction is on, this method
    // is called before each read, write, peek, or poke operation returns.
    // When auto-prediction is off, this method is called by a 
    // <uvm_reg_predictor> upon receipt and conversion of an observed bus
    // operation to this register.
    //
    // If a write prediction, the observed
    // write value is pushed to the abstract FIFO as long as it is 
    // not full and the operation did not originate from an <update()>.
    // If a read prediction, the observed read value is compared
    // with the frontmost value in the abstract FIFO if <set_compare()>
    // enabled comparison and the FIFO is not empty.
    //
    virtual function void do_predict(uvm_reg_item      rw,
                                     uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                     uvm_reg_byte_en_t be = -1);

      super.do_predict(rw,kind,be);

      if (rw.status == UVM_NOT_OK)
        return;

      case (kind)

        UVM_PREDICT_WRITE,
        UVM_PREDICT_DIRECT:
        begin
           if (fifo.size() != m_size && !m_update_in_progress)
             fifo.push_back(this.value.value);
        end

        UVM_PREDICT_READ:
        begin
           uvm_reg_data_t value = rw.value[0] & ((1 << get_n_bits())-1);
           uvm_reg_data_t mirror_val;
           if (fifo.size() == 0) begin
             return;
           end
           mirror_val = fifo.pop_front();
           if (this.value.get_compare() == UVM_CHECK && mirror_val != value) begin
              `uvm_warning("MIRROR_MISMATCH",
               $sformatf("Observed DUT read value 'h%0h != mirror value 'h%0h",value,mirror_val))
           end
        end

      endcase

    endfunction


    // Group -- NODOCS -- Special Overrides

    // Task -- NODOCS -- pre_write
    //
    // Special pre-processing for a <write()> or <update()>.
    // Called as a result of a <write()> or <update()>. It is an error to
    // attempt a write to a full FIFO or a write while an update is still
    // pending. An update is pending after one or more calls to <set()>.
    // If in your application the DUT allows writes to a full FIFO, you
    // must override ~pre_write~ as appropriate.
    //
    virtual task pre_write(uvm_reg_item rw);
      if (m_set_cnt && !m_update_in_progress) begin
        `uvm_error("Needs Update","Must call update() after set() and before write()")
        rw.status = UVM_NOT_OK;
        return;
      end
      if (fifo.size() >= m_size && !m_update_in_progress) begin
        `uvm_error("FIFO Full","Write to full FIFO ignored")
        rw.status = UVM_NOT_OK;
        return;
      end
    endtask


    // Task -- NODOCS -- pre_read
    //
    // Special post-processing for a <write()> or <update()>.
    // Aborts the operation if the internal FIFO is empty. If in your application
    // the DUT does not behave this way, you must override ~pre_write~ as
    // appropriate.
    //
    //
    virtual task pre_read(uvm_reg_item rw);
      // abort if fifo empty
      if (fifo.size() == 0) begin
        rw.status = UVM_NOT_OK;
        return;
      end
    endtask


    function void post_randomize();
      m_set_cnt = 0;
    endfunction

endclass
