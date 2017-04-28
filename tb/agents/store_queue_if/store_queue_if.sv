// Author: Florian Zaruba, ETH Zurich
// Date: 28.4.2017
// Description: Store Queue Interface
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

`ifndef STORE_QUEUE_IF_SV
`define STORE_QUEUE_IF_SV
interface store_queue_if
    #( parameter int ADDRESS_SIZE = 64,
       parameter int DATA_WIDTH = 64
    )
    (
        input clk
    );

   wire                     flush;
   wire [ADDRESS_SIZE-1:0]  check_paddr;
   wire [DATA_WIDTH-1:0]    check_data;
   wire                     valid;
   wire [DATA_WIDTH/8-1:0]  check_be;
   wire                     commit;
   wire                     ready;
   wire                     store_valid;
   wire [ADDRESS_SIZE-1:0]  store_paddr;
   wire [DATA_WIDTH-1:0]    store_data;
   wire [DATA_WIDTH/8-1:0]  store_be;

   clocking mck @(posedge clk);
        output  flush, commit, valid, store_paddr, store_data, store_be;
        input  check_paddr, check_data, check_be, ready, store_valid;

   endclocking


   clocking pck @(posedge clk);
     input  flush, check_paddr, check_data, valid, check_be, commit, ready, store_valid, store_paddr, store_data, store_be;
   endclocking

endinterface
`endif