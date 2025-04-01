// Copyright 2025 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Valentin Thomazic

`ifndef UTILS_MACROS_SVH
`define UTILS_MACROS_SVH

`define ASSERT_WARNING(msg)\
    `ifdef UVM\
        uvm_pkg::uvm_report_warning("ASSERT FAILED", msg, uvm_pkg::UVM_NONE, 1)\
    `else\
        $warning("%0t: ASSERT FAILED %0s", $time, msg)\
    `endif

`define ASSERT_ERROR(msg)\
    `ifdef UVM\
        uvm_pkg::uvm_report_error("ASSERT FAILED", msg, uvm_pkg::UVM_NONE, 1)\
    `else\
        $error("%0t: ASSERT FAILED %0s", $time, msg)\
    `endif

`define ASSERT_FATAL(msg)\
    `ifdef UVM\
        uvm_pkg::uvm_report_fatal("ASSERT FAILED", msg, uvm_pkg::UVM_NONE, 1)\
    `else\
        $fatal("%0t: ASSERT FAILED %0s", $time, msg)\
    `endif
`endif
