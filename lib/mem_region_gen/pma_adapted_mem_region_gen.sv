// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


class pma_adapted_memory_regions_c;

  typedef enum { PRINT_OFF, PRINT_VERBOSE, PRINT_DEBUG_LOW, PRINT_DEBUG_MED, PRINT_DEBUG_HIGH } print_verbosity_lvl_e;
  typedef enum { UNCHECKED, VALID, SPLIT, LB_ADJUST, UB_ADJUST, DISCARD } region_status_e;
  typedef enum { S_INIT, S_CHK_DONE, S_DONE, S_POP, S_CLASSIFY, S_CLASSIFY_DONE, S_INSERT, S_SPLIT_REGION, S_ADJUST_LOWER_BOUND, S_ADJUST_UPPER_BOUND, S_PUSH } fsm_state_e;

  typedef struct {
    pma_region_t cfg;
    int prio;
    region_status_e flag;
  } classified_region_t;

  parameter print_verbosity_lvl_e VERBOSITY_LVL = PRINT_VERBOSE;

  // This should be more than enough to complete in all cases for 16 regions
  // Prevents simulator freeze in case something goes awry and we end up not being able to classify a region
  parameter FSM_TIMEOUT_CYCLES = 100000;

  // Maximum size for the process_stack
  parameter MAX_PROCESS_STACK_SIZE = 2;

  static string info_tag = "pma_adapted_mem_region_c";

  // ##########################################################################
  // Public properties
  // ##########################################################################

  // Output data: Completely defined regions based on initial address map
  classified_region_t region[$];

  // ##########################################################################
  // Private properties
  // ##########################################################################

  // FSM State variables
  protected fsm_state_e state, next_state;

  // Stack that starts with the initial PMA regions, keeps to-be-done regions while processing
  protected classified_region_t stack[$];

  // Process stack, temporary stack that keeps splitted and processing in progress regions, should never exceed two elements
  protected classified_region_t process_stack[$];


  // ##########################################################################
  // Public methods
  // ##########################################################################

  /*
  * Function: new
  *
  * Inputs: pma_region_t pma_region[] - true pma configuration of the core
  *
  * Init function ,adds initial regions to the stack, classifies them as UNCHECKED
  * and initializes FSM
  */
  function new(pma_region_t pma_region[]);
    for (int i = pma_region.size() - 1; i >= 0; i--) begin
      // Skip zero-length regions
      if (pma_region[i].word_addr_low < pma_region[i].word_addr_high) begin
        add_region(pma_region[i], pma_region.size() - i, UNCHECKED);
      end
    end
    state      = S_INIT;
    next_state = S_INIT;
    fsm_state_behavior;
    divide_region_in_half(region);
  endfunction : new

  /*
  * Function: divide_region_in_half
  *
  * Inputs: ref classified_region_t region[$] - queue of classified regions
  *
  * By default riscv-dv depends on two memory pages - this function
  * aims to make sure that we always have two memory regions available.
  * It takes no action if the number of classified regions are != 1 or
  * if we for some reason (e.g. manual invocation for directed tests
  * want to disable the minimum two regions-requirement)
  */
  virtual function void divide_region_in_half(ref classified_region_t region[$]);
    bit require_min_two_region = 1;
    if (region.size() == 1 && require_min_two_region) begin
      region.push_back(region[0]);
      region[1].cfg.word_addr_low  = region[0].cfg.word_addr_high / 2;
      region[0].cfg.word_addr_high = region[1].cfg.word_addr_low  - 1;
    end
  endfunction : divide_region_in_half

  /*
  *  Task: check_regions
  *
  *  Depending on set VERBOSITY_LVL prints out:
  *    PRINT_VERBOSE   : prints generated region summary
  *
  */
  virtual function void check_regions;
    if (VERBOSITY_LVL >= PRINT_VERBOSE) begin
      foreach (region[i]) begin
        display_message($sformatf("Region_%-2d %-2d [32'h%08x:32'h%08x]", region[i].prio, i, region[i].cfg.word_addr_low<<2,  region[i].cfg.word_addr_high<<2), PRINT_VERBOSE);
      end // foreach
    end
  endfunction : check_regions

  // ##########################################################################
  // Private methods
  // ##########################################################################

  /*
  * Function: display_message
  *
  * Inputs:
  * string text     - text to display
  * print_verbosity_lvl_e verbosity_lvl - at what level of verbosity shall message be displayed
  *
  * Conditional printout of messages depending on configured verbosity level
  */
  protected virtual function void display_message(string text, print_verbosity_lvl_e verbosity_lvl);
    if (VERBOSITY_LVL >= verbosity_lvl) begin
      `ifdef uvm_info
        `uvm_info(info_tag, text, UVM_NONE)
      `else
        $display({ "[", info_tag, "] ", text });
      `endif
    end
  endfunction : display_message

  /*
  * Function: display_fatal
  *
  * Inputs:
  * string text     - text to display
  *
  * uvm/standalone compatibility function for $fatal/uvm_fatal
  */
  protected virtual function void display_fatal(string text);
    `ifdef uvm_fatal
      `uvm_fatal(info_tag, text)
    `else
      $fatal(1, { "[", info_tag, "] ", text });
    `endif
  endfunction : display_fatal

  /*
  * Function: add_region
  *
  * Inputs: pma_region_t    pma_region - Region to compute real bounds and insert into modified pma config stack
  *         int             pma_prio   - Priority of sampled PMA region (index in original array)
  *         region_status_e stack_flag - Region status flag
  *
  */
  protected virtual function void add_region(pma_region_t pma_region, int pma_prio, region_status_e stack_flag);
    pma_region.word_addr_high -= 1;
    stack.push_back('{cfg: pma_region, flag: stack_flag, prio: pma_prio});
  endfunction : add_region

  // --------------------------------------------------------------------------
  // FSM Processing Functions
  // --------------------------------------------------------------------------

  /*
  * Task: adjust_lower_bound
  *
  * Inputs:  ref classified_region_t proc_stack[$] - Stack for in-progress items
  *
  * Adjusts lower bound for the given region in case it overlaps with another higher priority region
  */
  protected virtual function automatic void adjust_lower_bound(ref classified_region_t proc_stack[$]);
    automatic bit bound_found = 0;
    foreach (region[i]) begin
      if (proc_stack[$].prio > region[i].prio) begin
        if (proc_stack[$].cfg.word_addr_low inside {[region[i].cfg.word_addr_low:region[i].cfg.word_addr_high]}) begin
          proc_stack[$].cfg.word_addr_low = region[i].cfg.word_addr_high + 1;
          bound_found = 1;
          break;
        end
      end
    end // foreach

    if (proc_stack[$].cfg.word_addr_low > proc_stack[$].cfg.word_addr_high || bound_found == 0) begin
      proc_stack[$].flag = DISCARD;
      display_message("DISCARDING", PRINT_DEBUG_MED);
    end else begin
      proc_stack[$].flag = UNCHECKED;
    end
  endfunction : adjust_lower_bound

  /*
  * Task: adjust_upper_bound
  *
  * Inputs:  ref classified_region_t proc_stack[$] - Stack for in-progress items
  *
  * Adjusts upper bound for the given region in case it intersects another higher priority region
  */
  protected virtual function automatic void adjust_upper_bound(ref classified_region_t proc_stack[$]);
    automatic bit bound_found = 0;
    foreach (region[i]) begin
      if (proc_stack[$].prio > region[i].prio) begin
        if (proc_stack[$].cfg.word_addr_high inside {[region[i].cfg.word_addr_low:region[i].cfg.word_addr_high]}) begin
          proc_stack[$].cfg.word_addr_high = region[i].cfg.word_addr_low - 1;
          bound_found = 1;
          break;
        end
      end
    end // foreach

    if (proc_stack[$].cfg.word_addr_low > proc_stack[$].cfg.word_addr_high || bound_found == 0) begin
      proc_stack[$].flag = DISCARD;
      display_message("DISCARDING", PRINT_DEBUG_MED);
    end else begin
      proc_stack[$].flag = UNCHECKED;
    end
  endfunction : adjust_upper_bound

  /*
  * Task: split_region
  *
  * Inputs:  ref classified_region_t proc_stack[$] - Stack for in-progress items
  *
  * Splits regions that intersect a higher prioritized (lower indexed) region at more than one point into two regions
  * and prepare these for adjustment.
  *
  */
  protected virtual function automatic void split_region(ref classified_region_t proc_stack[$]);
    proc_stack.push_back(proc_stack[$]);
    proc_stack[$-1].flag = UNCHECKED;
    proc_stack[$].flag   = UNCHECKED;

    // Split regions
    foreach (region[i]) begin
      if (proc_stack[$].prio > region[i].prio) begin
        if (proc_stack[$].cfg.word_addr_low < region[i].cfg.word_addr_low) begin
          proc_stack[$].cfg.word_addr_low    = region[i].cfg.word_addr_high + 1;
          proc_stack[$-1].cfg.word_addr_high = region[i].cfg.word_addr_low  - 1;
          break;
        end
      end
    end // foreach

    foreach (proc_stack[i]) begin
      display_message($sformatf("lo: %08x, hi: %08x", proc_stack[i].cfg.word_addr_low<<2, proc_stack[i].cfg.word_addr_high<<2), PRINT_DEBUG_HIGH);
    end
  endfunction : split_region

  /*
  * Task: classify_region
  *
  * Inputs:  ref classified_region_t proc_stack[$] - Stack for in-progress items
  *
  * Classifies regions into one of the following categories:
  * - LB_ADJUST: Lower bound (word_addr_low) is invalid, needs adjustment
  * - UB_ADJUST: Upper bound (word_addr_high) is invalid, needs adjustment
  * - SPLIT: Region transcends one or more regions, and must be split
  * - VALID: No issues found with current region, prepare for push to region stack
  */
  protected virtual function automatic void classify_region(ref classified_region_t proc_stack[$]);
    automatic bit lb_ok    = 1;
    automatic bit ub_ok    = 1;
    automatic bit no_split = 1;
    // Only UNCHECKED gets reclassified, others pass straight through
    case (proc_stack[$].flag)
      UNCHECKED: begin
        // Check for lower bound OK
        foreach (region[i]) begin
          if (proc_stack[$].cfg.word_addr_low inside {[region[i].cfg.word_addr_low:region[i].cfg.word_addr_high]}) begin
            lb_ok = 0;
            break;
          end
        end
        // Check for upper bound OK
        foreach (region[i]) begin
          if (proc_stack[$].cfg.word_addr_high inside {[region[i].cfg.word_addr_low:region[i].cfg.word_addr_high]}) begin
            ub_ok = 0;
            break;
          end
        end
        // Check if split is needed
        foreach (region[i]) begin
          if ((proc_stack[$].cfg.word_addr_low  < region[i].cfg.word_addr_low) &&
              (proc_stack[$].cfg.word_addr_high > region[i].cfg.word_addr_high)) begin
            no_split = 0;
            break;
          end
        end
        // Tag regions with necessary processing step
        priority casez ({lb_ok, ub_ok, no_split})
          3'b0??: proc_stack[$].flag = LB_ADJUST;
          3'b10?: proc_stack[$].flag = UB_ADJUST;
          3'b110: proc_stack[$].flag = SPLIT;
          3'b111: proc_stack[$].flag = VALID;
        endcase
        display_message($sformatf("Result: %0s", proc_stack[$].flag.name), PRINT_DEBUG_MED);
      end
    endcase
  endfunction : classify_region

  // --------------------------------------------------------------------------
  // FSM
  // --------------------------------------------------------------------------

  /*
  * Task: fsm_state_transitions
  *
  * Inputs: <none>
  *
  * FSM Next state logic
  */
  protected virtual function void fsm_state_transitions;
    case(state)
      S_INIT               : begin
        next_state               = S_CHK_DONE;
      end
      S_CHK_DONE           : begin
        case (stack.size)
          0         : next_state = S_DONE;
          default   : next_state = S_POP;
        endcase
      end
      S_POP                : begin
        next_state               = S_CLASSIFY;
      end
      S_CLASSIFY           : begin
        next_state               = S_CLASSIFY_DONE;
      end
      S_CLASSIFY_DONE      : begin
        case (process_stack[$].flag)
          UNCHECKED : next_state = S_PUSH;
          SPLIT     : next_state = S_SPLIT_REGION;
          LB_ADJUST : next_state = S_ADJUST_LOWER_BOUND;
          UB_ADJUST : next_state = S_ADJUST_UPPER_BOUND;
          VALID     : next_state = S_INSERT;
          DISCARD   : next_state = S_CHK_DONE;
        endcase
      end
      S_INSERT             : begin
        next_state               = S_CHK_DONE;
      end
      S_SPLIT_REGION       : begin
        next_state               = S_PUSH;
      end
      S_ADJUST_LOWER_BOUND : begin
        next_state               = S_PUSH;
      end
      S_ADJUST_UPPER_BOUND : begin
        next_state               = S_PUSH;
      end
      S_PUSH               : begin
        case (process_stack.size)
          0       : next_state  = S_POP;
          default : next_state  = S_PUSH;
        endcase
      end
      S_DONE               : begin
        next_state              = S_DONE;
      end
    endcase
  endfunction : fsm_state_transitions

  /*
  * Task: fsm_state_behavior
  *
  * Inputs: <none>
  *
  * FSM output logic
  */
  protected virtual function void fsm_state_behavior;
    automatic int state_behav_ctr;

    forever begin
      state_behav_ctr += 1;
      display_message($sformatf("FSM Iteration: %0d", state_behav_ctr), PRINT_DEBUG_HIGH);
      case(state)
        S_INIT : begin
          display_message("S_INIT", PRINT_DEBUG_LOW);
        end
        S_CHK_DONE : begin
          display_message("S_CHK_DONE", PRINT_DEBUG_LOW);
        end
        S_POP : begin
          display_message("S_POP", PRINT_DEBUG_LOW);
          process_stack.push_back(stack.pop_front);
          display_message($sformatf("S_POP [0x%08x:0x%08x]", process_stack[$].cfg.word_addr_low<<2, process_stack[$].cfg.word_addr_high<<2), PRINT_DEBUG_MED);
        end
        S_CLASSIFY : begin
          display_message("S_CLASSIFY", PRINT_DEBUG_LOW);
          classify_region(process_stack);
        end
        S_CLASSIFY_DONE : begin
          display_message("S_CLASSIFY_DONE", PRINT_DEBUG_LOW);
          display_message($sformatf("stack: %0s", process_stack[$].flag.name), PRINT_DEBUG_MED);
        end
        S_INSERT : begin
          display_message("S_INSERT", PRINT_DEBUG_LOW);
          region.push_back(process_stack.pop_front);
          display_message($sformatf("S_INSERT [0x%08x:0x%08x]", region[$].cfg.word_addr_low<<2, region[$].cfg.word_addr_high<<2), PRINT_DEBUG_MED);
        end
        S_SPLIT_REGION : begin
          display_message("S_SPLIT_REGION", PRINT_DEBUG_LOW);
          split_region(process_stack);
        end
        S_ADJUST_LOWER_BOUND : begin
          display_message("S_ADJUST_LOWER_BOUND", PRINT_DEBUG_LOW);
          adjust_lower_bound(process_stack);
        end
        S_ADJUST_UPPER_BOUND : begin
          display_message("S_ADJUST_UPPER_BOUND", PRINT_DEBUG_LOW);
          adjust_upper_bound(process_stack);
        end
        S_PUSH : begin
          display_message("S_PUSH", PRINT_DEBUG_LOW);
          stack.push_front(process_stack.pop_back);
        end
        S_DONE : begin
          display_message("S_DONE", PRINT_DEBUG_LOW);
          break;
        end
      endcase
      // In lieu of creating a typed queue to restrict size of process_stack, do a check on max size here to ensure the queue
      // does not grow beyond expected bounds
      if (process_stack.size() > MAX_PROCESS_STACK_SIZE) begin
        `uvm_fatal("PMAPROCSTACK", $sformatf("process_stack size of %0d is greater than maximum allowed: %0s", process_stack.size(), MAX_PROCESS_STACK_SIZE));
      end

      fsm_state_transitions;
      state = next_state;
      if (state_behav_ctr >= FSM_TIMEOUT_CYCLES) begin
        display_fatal("TIMEOUT occured - FSM exceeded maxium allowed compute cycles!");
      end
      display_message($sformatf("Next state: %s", next_state.name), PRINT_DEBUG_HIGH);
    end // forever
  endfunction : fsm_state_behavior

endclass : pma_adapted_memory_regions_c
