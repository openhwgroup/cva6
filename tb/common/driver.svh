// Author: Florian Zaruba, ETH Zurich, Robert Schilling, TU Graz
// Date: 27.04.2017
// Description: Abstract Driver Class, similar to a UVM Driver
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
class driver #(type dut_t);

  // Virtual interface to the design under verification (DUT).
  virtual dut_t dut_if;

  // The mailbox for providing stimuli data to the monitor.
  mailbox #(sequence_item) mbx;

  // run task which drives the stimuli
  virtual task run(mailbox mbx);

  endtask : run

  // --------------
  // Constructors
  // --------------
  function new ( virtual dut_t dut_if, mailbox mbx);
    // Connect the DUV interface.
    this.dut_if = dut_if;
    this.mbx    = mbx;
  endfunction


endclass : driver