// Author: Florian Zaruba, ETH Zurich
// Date: 8.5.2017
// Description: Core Interface
//
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
`ifndef CORE_IF_SV
`define CORE_IF_SV
interface core_if (
        input clk
    );

    wire clock_en;
    wire test_en;
    wire fetch_enable;
    wire core_busy;
    wire [63:0] boot_addr;
    wire [3:0] core_id;
    wire [5:0] cluster_id;
    wire irq;
    wire [4:0] irq_id;
    wire irq_ack;
    wire irq_sec;
    wire sec_lvl;

   clocking mck @(posedge clk);
        output clock_en, test_en, fetch_enable, boot_addr, core_id, cluster_id, irq, irq_id, irq_sec;
        input  core_busy, sec_lvl, irq_ack;
   endclocking

   clocking pck @(posedge clk);
        input  clock_en, test_en, fetch_enable, boot_addr, core_id, cluster_id, irq, irq_id, irq_sec, core_busy, sec_lvl, irq_ack;
   endclocking

endinterface
`endif