//
//----------------------------------------------------------------------
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2011 AMD
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
//----------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_task_phase
//
//------------------------------------------------------------------------------
// Base class for all task phases.
// It forks a call to <uvm_phase::exec_task()>
// for each component in the hierarchy.
//
// The completion of the task does not imply, nor is it required for, 
// the end of phase. Once the phase completes, any remaining forked 
// <uvm_phase::exec_task()> threads are forcibly and immediately killed.
//
// By default, the way for a task phase to extend over time is if there is
// at least one component that raises an objection.  
//| class my_comp extends uvm_component;
//|    task main_phase(uvm_phase phase);
//|       phase.raise_objection(this, "Applying stimulus")
//|       ...
//|       phase.drop_objection(this, "Applied enough stimulus")
//|    endtask
//| endclass
// 
//   
// There is however one scenario wherein time advances within a task-based phase
// without any objections to the phase being raised. If two (or more) phases 
// share a common successor, such as the <uvm_run_phase> and the 
// <uvm_post_shutdown_phase> sharing the <uvm_extract_phase> as a successor, 
// then phase advancement is delayed until all predecessors of the common 
// successor are ready to proceed.  Because of this, it is possible for time to 
// advance between <uvm_component::phase_started> and <uvm_component::phase_ended>
// of a task phase without any participants in the phase raising an objection.
//

// @uvm-ieee 1800.2-2017 auto 9.6.1
virtual class uvm_task_phase extends uvm_phase;



  // @uvm-ieee 1800.2-2017 auto 9.6.2.1
  function new(string name);
    super.new(name,UVM_PHASE_IMP);
  endfunction



  // @uvm-ieee 1800.2-2017 auto 9.6.2.2
  virtual function void traverse(uvm_component comp,
                                 uvm_phase phase,
                                 uvm_phase_state state);
    phase.m_num_procs_not_yet_returned = 0;
    m_traverse(comp, phase, state);
  endfunction

  function void m_traverse(uvm_component comp,
                           uvm_phase phase,
                           uvm_phase_state state);
    string name;
    uvm_domain phase_domain =phase.get_domain();
    uvm_domain comp_domain = comp.get_domain();
    uvm_sequencer_base seqr;
    
    if (comp.get_first_child(name))
      do
        m_traverse(comp.get_child(name), phase, state);
      while(comp.get_next_child(name));

    if (m_phase_trace)
    `uvm_info("PH_TRACE",$sformatf("topdown-phase phase=%s state=%s comp=%s comp.domain=%s phase.domain=%s",
          phase.get_name(), state.name(), comp.get_full_name(),comp_domain.get_name(),phase_domain.get_name()),
          UVM_DEBUG)

    if (phase_domain == uvm_domain::get_common_domain() ||
        phase_domain == comp_domain) begin
      case (state)
        UVM_PHASE_STARTED: begin
          comp.m_current_phase = phase;
          comp.m_apply_verbosity_settings(phase);
          comp.phase_started(phase);
          if ($cast(seqr, comp))
            seqr.start_phase_sequence(phase);
          end
        UVM_PHASE_EXECUTING: begin
          uvm_phase ph = this; 
          if (comp.m_phase_imps.exists(this))
            ph = comp.m_phase_imps[this];
          ph.execute(comp, phase);
          end
        UVM_PHASE_READY_TO_END: begin
          comp.phase_ready_to_end(phase);
          end
        UVM_PHASE_ENDED: begin
          if ($cast(seqr, comp))
            seqr.stop_phase_sequence(phase);
          comp.phase_ended(phase);
          comp.m_current_phase = null;
          end
        default:
          `uvm_fatal("PH_BADEXEC","task phase traverse internal error")
      endcase
    end

  endfunction



  // @uvm-ieee 1800.2-2017 auto 9.6.2.3
  virtual function void execute(uvm_component comp,
                                          uvm_phase phase);

    fork
      begin
        process proc;

        // reseed this process for random stability
        proc = process::self();
        proc.srandom(uvm_create_random_seed(phase.get_type_name(), comp.get_full_name()));

        phase.m_num_procs_not_yet_returned++;

        exec_task(comp,phase);

        phase.m_num_procs_not_yet_returned--;

      end
    join_none

  endfunction
endclass
