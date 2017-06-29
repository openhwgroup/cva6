// Author: Florian Zaruba, ETH Zurich
// Date: 16.05.2017
// Description: Instruction Tracer Package
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
package instruction_tracer_pkg;
    import ariane_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    `include "instruction_tracer_defines.svh"
    `include "instruction_trace_item.svh"
    `include "exception_trace_item.svh"
    `include "instruction_tracer.svh"
endpackage