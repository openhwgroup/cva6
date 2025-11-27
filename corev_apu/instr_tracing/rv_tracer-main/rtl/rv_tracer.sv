// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51

// Author:  Umberto Laghi
// Contact: umberto.laghi2@unibo.it
// Github:  @ubolakes

/* TOP LEVEL MODULE */

module rv_tracer #(
    //parameter IRETIRE_LEN = 32, // set to 1 for single retirement
    parameter N = 1, // max number of special inst retired in a cycle, the input port number depends on this value
    parameter ONLY_BRANCHES = 0, // special inst are branches or not
    parameter APB_ADDR_WIDTH = 32 // address width for APB interface
)
(
    input logic                                     clk_i,
    input logic                                     rst_ni,

    input logic [N-1:0]                             valid_i, // used for multiple retirement

    /* data from the CPU */
    // mandatory inputs
    input logic [N-1:0][te_pkg::ITYPE_LEN-1:0]      itype_i, // termination type of block
    input logic [te_pkg::XLEN-1:0]                  cause_i,
    input logic [te_pkg::XLEN-1:0]                  tval_i,
    input logic [te_pkg::PRIV_LEN-1:0]              priv_i,
    input logic [N-1:0][te_pkg::XLEN-1:0]           iaddr_i, // pc of 1st inst in block
    input logic [N-1:0][te_pkg::IRETIRE_LEN-1:0]    iretire_i, // length of block in halfwords
    input logic [N-1:0]                             ilastsize_i, // length of last inst in 2^ilastsize halfword
    // non mandatory inputs
    input logic [te_pkg::TIME_LEN-1:0]              time_i,
    //input logic [:0]                                context_i,
    //input logic [te_pkg::CTYPE_LEN-1:0]             ctype_i, // spec says it's 1 or 2 bit wide
    //input logic [te_pkg::TRIGGER_LEN-1:0]           trigger_i, // must be supported CPU side

    // support inputs
    input logic [te_pkg::XLEN-1:0]                  tvec_i, // tvec_q, contains trap handler address
    input logic [te_pkg::XLEN-1:0]                  epc_i, // epc_q, required for format 3 subformat 1
    input logic                                     encapsulator_ready_i, // non mandatory
    
    // APB interface inputs
    input logic [APB_ADDR_WIDTH-1:0]                paddr_i,
    input logic                                     pwrite_i,
    input logic                                     psel_i,
    input logic                                     penable_i,
    input logic [31:0]                              pwdata_i,
    
    // outputs
    // info needed for the encapsulator
    output logic [N-1:0]                            packet_valid_o,
    output te_pkg::it_packet_type_e [N-1:0]         packet_type_o,
    output logic [N-1:0][te_pkg::P_LEN-1:0]         packet_length_o, // in bytes
    output logic [N-1:0][te_pkg::PAYLOAD_LEN-1:0]   packet_payload_o,
    // sideband signals
    output logic                                    stall_o,

    // APB interface outputs
    output logic                                    pready_o,
    output logic [31:0]                             prdata_o
);

    /* signals for management */
    // registers
    logic                                   trace_activated;
    logic                                   trace_enable;
    logic                                   nocontext;
    logic                                   notime;
    logic                                   encoder_mode;
    // filter
    logic                                   trigger_trace_on; // hardwired to 0?
    logic                                   trigger_trace_off; // hardwired to 0?
    //logic                                   qualified; // is it needed or I can use qualified_d?
    logic                                   trace_req_deactivate;
    // priority
    te_pkg::format_e                        packet_format[N-1:0];
    te_pkg::f_sync_subformat_e              packet_f_sync_subformat[N-1:0];
    te_pkg::f_opt_ext_subformat_e           packet_f_opt_ext_subformat[N-1:0];
    logic                                   thaddr[N-1:0];
    logic                                   lc_tc_mux[N-1:0];
    te_pkg::qual_status_e                   qual_status[N-1:0];
    logic                                   nc_branch_map_flush;
    logic [te_pkg::BRANCH_MAP_LEN-1:0]      branch_map;
    logic [te_pkg::BRANCH_COUNT_LEN-1:0]    branch_count;
    logic                                   resync_rst;
    // packet emitter
    logic                                   packet_valid[N-1:0];
    // resync counter
    logic [N-1:0]                           packet_emitted;
    // not classified
    logic                                   nc_branch_map_empty;
    logic                                   clk_gated;
    logic                                   turn_on_tracer_d, turn_on_tracer_q;
    logic                                   lossless_trace;
    logic                                   shallow_trace;

    // we have three phases, called last cycle (lc), this cycle (tc) and next
    // cycle (nc), based on which we make decision whether we need to emit a
    // packet or not.
    logic                                   tc_branch_map_empty;
    logic [N-1:0]                           tc_resync;
    logic [N-1:0]                           nc_exc_only;
    logic [N-1:0]                           nc_ppccd_br;
    logic [$clog2(te_pkg::XLEN):0]          keep_bits[N-1:0];
    logic [te_pkg::XLEN-1:0]                addr_to_compress[N-1:0];

    logic [1:0][N-1:0][te_pkg::IRETIRE_LEN-1:0] iretired_tab;
    logic [2:0]                                 exception_tab;
    logic [2:0]                                 interrupt_tab;
    logic [2:0][te_pkg::XLEN-1:0]               cause_tab;
    logic [1:0][te_pkg::XLEN-1:0]               tvec_tab;
    logic [2:0][te_pkg::XLEN-1:0]               tval_tab;
    logic [1:0][N-1:0][te_pkg::ITYPE_LEN-1:0]   itype_tab;
    logic [1:0][te_pkg::PRIV_LEN-1:0]           priv_tab;
    logic [1:0][N-1:0][te_pkg::XLEN-1:0]        address_tab;
    logic [2:0][te_pkg::XLEN-1:0]               epc_tab;
    logic [1:0][te_pkg::TIME_LEN-1:0]           time_tab;
    logic [2:0][N-1:0]                          updiscon_tab;
    logic [2:0][N-1:0]                          qualified_tab;
   
    logic [N-1:0][te_pkg::IRETIRE_LEN-1:0]  tc_iretired, nc_iretired;
    logic                                   lc_exception, tc_exception, nc_exception;
    logic                                   lc_interrupt, tc_interrupt, nc_interrupt;
    logic [te_pkg::XLEN-1:0]                lc_cause, tc_cause, nc_cause;
    logic [te_pkg::XLEN-1:0]                tc_tvec, nc_tvec;
    logic [te_pkg::XLEN-1:0]                lc_tval, tc_tval, nc_tval;
    logic [N-1:0][te_pkg::ITYPE_LEN-1:0]    tc_itype, nc_itype;
    logic [te_pkg::PRIV_LEN-1:0]            tc_priv, nc_priv;
    logic [N-1:0][te_pkg::XLEN-1:0]         tc_address, nc_address;
    logic [te_pkg::XLEN-1:0]                lc_epc, tc_epc, nc_epc;                 
    logic [te_pkg::TIME_LEN-1:0]            tc_time, nc_time;
    logic [N-1:0]                           lc_updiscon, tc_updiscon, nc_updiscon;
    logic [N-1:0]                           lc_qualified, tc_qualified, nc_qualified;

   
    logic                                   tc_first_qualified;
    logic                                   tc_final_qualified;
    logic [N-1:0]                           updiscon;
    logic [N-1:0][te_pkg::XLEN-1:0]         address;
    logic [N-1:0]                           qualified;
    
    
    logic [N-1:0]                           valid0_d, valid0_q;
    logic                                   privchange_d, privchange_q;
    // logic                                   context_change_d, context_change_q; // non mandatory
    // logic                                   precise_context_report_d, precise_context_report_q; // requires ctype signal CPU side
    // logic                                   context_report_as_disc_d, context_report_as_disc_q; // ibidem
    // logic                                   no_context_report_d, no_context_report_q; // ibidem
    // logic                                   imprecise_context_report_d, imprecise_context_report_q; // ibidem
    logic                                   gt_max_resync_d, gt_max_resync_q;
    logic                                   et_max_resync_d, et_max_resync_q;
    logic                                   branch_map_full_d, branch_map_full_q;
    //logic                                   branch_misprediction_d, branch_misprediction_q; // non mandatory
    logic                                   trace_activated_d, trace_activated_q;
    logic                                   enc_activated_d, enc_activated_q;
    logic                                   enc_deactivated_d, enc_deactivated_q;
    //logic                                   packets_lost_d, packets_lost_q; // non mandatory
    te_pkg::ioptions_s                      enc_config_d, enc_config_q;
    logic                                   enc_config_change_d, enc_config_change_q;
    logic                                   branch_d, branch_q;
    logic                                   branch_taken_d, branch_taken_q;
    
    // branch_map inputs
    logic [N-1:0]   branch_valid;
    logic [N-1:0]   branch_taken;
    
    // te_reg output to filter input
    logic                           cause_filter;
    logic [te_pkg::XLEN-1:0]        upper_cause;
    logic [te_pkg::XLEN-1:0]        lower_cause;
    logic [te_pkg::XLEN-1:0]        match_cause;
    logic                           cause_mode;
    logic                           tvec_filter;
    logic [te_pkg::XLEN-1:0]        upper_tvec;
    logic [te_pkg::XLEN-1:0]        lower_tvec;
    logic [te_pkg::XLEN-1:0]        match_tvec;
    logic                           tvec_mode;
    logic                           tval_filter;
    logic [te_pkg::XLEN-1:0]        upper_tval;
    logic [te_pkg::XLEN-1:0]        lower_tval;
    logic [te_pkg::XLEN-1:0]        match_tval;
    logic                           tval_mode;
    logic                           priv_lvl_filter;
    logic [te_pkg::PRIV_LEN-1:0]    upper_priv;
    logic [te_pkg::PRIV_LEN-1:0]    lower_priv;
    logic [te_pkg::PRIV_LEN-1:0]    match_priv;
    logic                           priv_lvl_mode;
    logic                           iaddr_filter;
    logic [te_pkg::XLEN-1:0]        upper_iaddr;
    logic [te_pkg::XLEN-1:0]        lower_iaddr;
    logic [te_pkg::XLEN-1:0]        match_iaddr;
    logic                           iaddr_mode;

    /*  the following commented section has non mandatory signals
        for now it's commented
    */
 /* combinatorial network to define the following 
    signals from ctype:
    - tc_no_context_report_i        -> ctype == 0
    - tc_precise_context_report_i   -> ctype == 2
    - tc_context_report_as_disc_i   -> ctype == 3
    - tc_imprecise_context_report_i -> ctype == 1
    - nc_precise_context_report_i   -> ctype == 2
    - nc_context_report_as_disc_i   -> ctype == 3*/
    /*
    always_comb begin : ctype_manager
        case(ctype_i)
        2'h0: // no report - add signal        
            tc_no_context_report = '1;
        2'h1:
            tc_imprecise_context_report = '1;
        2'h2:
            tc_precise_context_report = '1;
        2'h3:
            tc_context_report_as_disc = '1;
        endcase
    end
    */

    /*TODO: create a trigger decoder that produces:
                - trigger_trace_on  -> 2
                - trigger_trace_off -> 3
                - trigger_notify    -> 4
    */
    // maybe it's enough to define values and hardwire them to 0

    /* ASSIGNMENT */
    /* hardwired assignments */
    assign trigger_trace_on = '0;
    assign trigger_trace_off = '0;

    /* FFs inputs */
    assign valid0_d = valid_i;
    assign trace_activated_d = trace_activated;
    assign enc_activated_d = trace_activated_d && ~trace_activated_q;
    assign enc_deactivated_d = ~trace_activated_d && trace_activated_q;
    assign enc_config_change_d = enc_config_d != enc_config_q;

    /* next cycle */
    assign nc_branch_map_empty = nc_branch_map_flush || (tc_branch_map_empty /*&& ~branch_q*/);

    // output
    assign packet_valid_o = packet_emitted;
    // sideband
    assign stall_o = ~encapsulator_ready_i && lossless_trace;

    // other
    assign branch_taken_d = |branch_taken;

    // first and final qualified
    assign tc_first_qualified = trace_activated && |tc_qualified && !lc_qualified && trace_enable;
    assign tc_final_qualified = trace_activated && |lc_qualified && !tc_qualified && trace_enable;

    always_ff @( posedge clk_i, negedge rst_ni ) begin 
        if(~rst_ni) begin
            iretired_tab  <= '0;
            exception_tab <= '0;
            interrupt_tab <= '0;
            cause_tab <= '0;
            tvec_tab <= '0;
            tval_tab <= '0;
            itype_tab <= '0;
            priv_tab <= '0;
            address_tab <= '0;
            epc_tab <= '0;
            time_tab <= '0;
            updiscon_tab <= '0;
            qualified_tab <= '0;
        end else begin
            if (|valid_i) begin 
                iretired_tab <= {iretired_tab[0], iretire_i};
                exception_tab <= {exception_tab[1:0], itype_i[0] == 1};
                interrupt_tab <= {interrupt_tab[1:0], itype_i[0] == 2};
                cause_tab <= {cause_tab[1:0],cause_i};
                tvec_tab <= {tvec_tab[0], tvec_i};
                tval_tab <= {tval_tab [1:0], tval_i};
                itype_tab <= {itype_tab[0], itype_i};
                priv_tab <= {priv_tab[0], priv_i};
                address_tab <= {address_tab[0], address};
                epc_tab <= {epc_tab[1:0], epc_i};
                time_tab <= {time_tab[0], time_i};
                updiscon_tab <= {updiscon_tab[1:0], updiscon};
                qualified_tab <={qualified_tab[1:0], qualified};
            end
        end 

    end 
    //lc asignements
    assign lc_exception = exception_tab[2];
    assign lc_interrupt = interrupt_tab[2];
    assign lc_cause = cause_tab[2];
    assign lc_tval = tval_tab[2];
    assign lc_epc = epc_tab[2];
    assign lc_updiscon = updiscon_tab[2];
    assign lc_qualified = qualified_tab[2];    
    // tc assignements
    assign tc_iretired = iretired_tab[1];
    assign tc_exception = exception_tab[1];
    assign tc_interrupt = interrupt_tab[1];
    assign tc_cause= cause_tab[1];
    assign tc_tvec = tvec_tab[1];
    assign tc_tval = tval_tab[1];
    assign tc_itype = itype_tab[1];
    assign tc_priv = priv_tab[1];
    assign tc_address = address_tab[1];
    assign tc_epc = epc_tab[1];
    assign tc_time = time_tab[1];
    assign tc_updiscon = updiscon_tab[1];
    assign tc_qualified = qualified_tab[1];

       // nc assignements
    assign nc_iretired = iretired_tab[0];
    assign nc_exception = exception_tab[0];
    assign nc_interrupt = interrupt_tab[0];
    assign nc_cause= cause_tab[0];
    assign nc_tvec = tvec_tab[0];
    assign nc_tval = tval_tab[0];
    assign nc_itype = itype_tab[0];
    assign nc_priv = priv_tab[0];
    assign nc_address = address_tab[0];
    assign nc_epc = epc_tab[0];
    assign nc_time = time_tab[0];
    assign nc_updiscon = updiscon_tab[0];
    assign nc_qualified = qualified_tab[0]; 

    //FIXME need cleaning
    // not static assignments
    always_comb begin
        // init
        branch_valid = '0;
        branch_taken = '0;
        
        privchange_d = privchange_q;
        // context_change_d = context_change_q;
        // precise_context_report_d = precise_context_report_q; // requires ctype signal CPU side
        // context_report_as_disc_d = context_report_as_disc_q; //ibidem
        // no_context_report_d = no_context_report_q; // ibidem
        // imprecise_context_report_d = imprecise_context_report_q; // ibidem
        branch_d = branch_q;

        // itype, iretired and address
        // it works for all three cases
        for (int i = 0; i < N; i++) begin
            if (valid_i[i]) begin
                address[i] = iaddr_i[i];
                //FIXME we remove block reconstruction address
                //address[i] = iaddr_i[i]+2*(iretire_i[i] - 2**ilastsize_i[i]);
            end
        end
        //FIXME weird timing here nc for erveryone ?
        // assigning branch map inputs
        for (int i = 0; i < N; i++) begin
            if (nc_itype[i] == 4 || nc_itype[i] == 5) begin
                branch_valid[i] = '1;
            end
            if (nc_itype[i] == 5) begin
                branch_taken[i] = '1;
            end
        end

        // updiscon
        if (N == 1 || (N > 1 && ONLY_BRANCHES)) begin
            if (qualified[0]) begin
                updiscon[0] = itype_i[0] == 6;
            end
        end
        // wait for this case
        if (N > 1 && !ONLY_BRANCHES) begin
            for (int i = 0; i < N; i++) begin
                if (qualified[i]) begin
                    updiscon[i] = itype_i[i] == 6;
                end
            end
        end

        // updating registers values
        if (|valid_i) begin
            privchange_d = (nc_priv != tc_priv) && |valid_i;
            // context_change_d; // TODO
            //precise_context_report_d; // requires ctype signal CPU side
            //context_report_as_disc_d; //ibidem
            //no_context_report_d; // ibidem
            //imprecise_context_report_d; // ibidem
            branch_d = |branch_valid;
        end

        if (!turn_on_tracer_q) begin
            turn_on_tracer_d = |valid_i && nc_qualified;
        end
    end

    /* MODULES INSTANTIATION */
    // one instance for all 3 cases
    

    /* MAPPED REGISTERS */
    te_reg #(
        .APB_ADDR_WIDTH(APB_ADDR_WIDTH)
    ) i_te_reg(
        .clk_i               (clk_i),
        .rst_ni              (rst_ni),
        .trace_req_off_i     ('0), 
        .trace_req_on_i      (turn_on_tracer_q), // trigger_trace_on      // from trigger unit
        .encapsulator_ready_i(encapsulator_ready_i),
        .cause_filter_o      (cause_filter),
        .upper_cause_o       (upper_cause),
        .lower_cause_o       (lower_cause),
        .match_cause_o       (match_cause),
        .cause_mode_o        (cause_mode),
        .tvec_filter_o       (tvec_filter),
        .upper_tvec_o        (upper_tvec),
        .lower_tvec_o        (lower_tvec),
        .match_tvec_o        (match_tvec),
        .tvec_mode_o         (tvec_mode),
        .tval_filter_o       (tval_filter),
        .upper_tval_o        (upper_tval),
        .lower_tval_o        (lower_tval),
        .match_tval_o        (match_tval),
        .tval_mode_o         (tval_mode),
        .priv_lvl_filter_o   (priv_lvl_filter),
        .upper_priv_o        (upper_priv),
        .lower_priv_o        (lower_priv),
        .match_priv_o        (match_priv),
        .priv_lvl_mode_o     (priv_lvl_mode),
        .iaddr_filter_o      (iaddr_filter),
        .upper_iaddr_o       (upper_iaddr),
        .lower_iaddr_o       (lower_iaddr),
        .match_iaddr_o       (match_iaddr),
        .iaddr_mode_o        (iaddr_mode),
        .trace_enable_o      (trace_enable),
        .trace_activated_o   (trace_activated),
        .nocontext_o         (nocontext),
        .notime_o            (notime),
        .encoder_mode_o      (encoder_mode),
        .configuration_o     (enc_config_d),
        .lossless_trace_o    (lossless_trace),
        .shallow_trace_o     (shallow_trace),
        .clk_gated_o         (clk_gated),
        .paddr_i             (paddr_i),
        .pwrite_i            (pwrite_i),
        .psel_i              (psel_i),
        .penable_i           (penable_i),
        .pwdata_i            (pwdata_i),
        .pready_o            (pready_o),
        .prdata_o            (prdata_o)
    );

    /* BRANCH MAP */
    te_branch_map #(
        .N(N)
    ) i_te_branch_map(
        .clk_i         (clk_gated),
        .rst_ni        (rst_ni),
        .valid_i       (branch_valid & nc_qualified & valid0_q),
        .branch_taken_i(branch_taken),
        .flush_i       (nc_branch_map_flush),
        //.branch_taken_prediction_i(), // non mandatory
        .map_o         (branch_map),
        .branches_o    (branch_count),
        //.pbc_o(), // non mandatory - branch prediction mode
        //.misprediction_o(), // non mandatory - ibidem
        .is_full_o     (branch_map_full_d),
        .is_empty_o    (tc_branch_map_empty)
    );

    /* RESYNC COUNTER */
    te_resync_counter #(
        .N(N), 
        .MODE(te_pkg::CYCLE_MODE), // count cycles
        .MAX_VALUE(13'h1FFF)         // 8192
    ) i_te_resync_counter( // for testing we keep the def settings
        .clk_i           (clk_gated),
        .rst_ni          (rst_ni),
        .trace_enabled_i (trace_enable),
        .packet_emitted_i(packet_emitted),
        .resync_rst_i    (resync_rst),
        .gt_resync_max_o (gt_max_resync_d),
        .et_resync_max_o (et_max_resync_d)
    );

    // N instances for all 3 cases

    /* FILTER */
    generate
        if (ONLY_BRANCHES) begin
            for (genvar i = 0; i < N; i++) begin
                te_filter i_te_filter(
                    .trace_enable_i   (trace_enable || trace_activated), // tracks 1st branch if 1st inst
                    .cause_filter_i   (cause_filter),
                    .upper_cause_i    (upper_cause),
                    .lower_cause_i    (lower_cause),
                    .match_cause_i    (match_cause),
                    .cause_mode_i     (cause_mode),
                    .cause_i          (cause_i),
                    .tvec_filter_i    (tvec_filter),
                    .upper_tvec_i     (upper_tvec),
                    .lower_tvec_i     (lower_tvec),
                    .match_tvec_i     (match_tvec),
                    .tvec_mode_i      (tvec_mode),
                    .tvec_i           (tvec_i),
                    .tval_filter_i    (tval_filter),
                    .upper_tval_i     (upper_tval),
                    .lower_tval_i     (lower_tval),
                    .match_tval_i     (match_tval),
                    .tval_mode_i      (tval_mode),
                    .tval_i           (tval_i),
                    .priv_lvl_filter_i(priv_lvl_filter),
                    .upper_priv_i     (upper_priv),
                    .lower_priv_i     (lower_priv),
                    .match_priv_i     (match_priv),
                    .priv_lvl_mode_i  (priv_lvl_mode),
                    .priv_i           (priv_i),
                    .iaddr_filter_i   (iaddr_filter),
                    .upper_iaddr_i    (upper_iaddr),
                    .lower_iaddr_i    (lower_iaddr),
                    .match_iaddr_i    (match_iaddr),
                    .iaddr_mode_i     (iaddr_mode),
                    .iaddr_i          (iaddr_i[i]),
                    .nc_qualified_o   (qualified[i])
                );
            end
        end
    endgenerate

    /* PRIORITY, PACKET EMITTER*/
    // case dependant
    generate
        // 1 instance for N == 1 || (N > 1 && ONLY_BRANCHES)
        if (N == 1 || (N > 1 && ONLY_BRANCHES)) begin
            /* PRIORITY */
            te_priority i_te_priority(
                .clk_i                    (clk_gated),
                .rst_ni                   (rst_ni),
                .valid_i                  (valid0_q[0] || (enc_activated_q || enc_deactivated_q)), // necessary to generate F3SF3 packet
                .lc_exception_i           (lc_exception || lc_interrupt),
                .lc_updiscon_i            (lc_updiscon),
                .tc_qualified_i           (tc_qualified[0]),
                .tc_exception_i           (tc_exception|| tc_interrupt),
                .tc_retired_i             (tc_iretired[0]),
                .tc_first_qualified_i     (tc_first_qualified),
                .tc_privchange_i          (privchange_q),
                //.tc_context_change_i(), // non mandatory
                //.tc_precise_context_report_i(), // requires ctype signal CPU side
                //.tc_context_report_as_disc_i(), // ibidem
                //.tc_imprecise_context_report_i(), // ibidem
                .tc_gt_max_resync_i       (gt_max_resync_q),
                .tc_et_max_resync_i       (et_max_resync_q),
                .tc_branch_map_empty_i    (tc_branch_map_empty),
                .tc_branch_map_full_i     (branch_map_full_d),
                //.tc_branch_misprediction_i(), // non mandatory
                //.tc_pbc_i(), // non mandatory
                .tc_enc_enabled_i         (enc_activated_q),
                .tc_enc_disabled_i        (enc_deactivated_q),
                .tc_opmode_change_i       (enc_config_change_q),
                .tc_final_qualified_i     (tc_final_qualified),
                .tc_packets_lost_i        (~encapsulator_ready_i), // non mandatory
                .nc_exception_i           (nc_exception || nc_interrupt),
                .nc_privchange_i          (privchange_d), 
                //.nc_context_change_i(),
                //.nc_precise_context_report_i(), // requires ctype signal CPU side
                //.nc_context_report_as_disc_i(), // ibidem
                .nc_branch_map_empty_i    (nc_branch_map_empty),
                .nc_qualified_i           (nc_qualified[0]),
                .nc_retired_i             (nc_iretired[0]),
                //.halted_i(), // non mandatory side band signal
                //.reset_i(), // ibidem
                //.implicit_return_i(), // non mandatory
                //.tc_trigger_req_i(), // non mandatory
                //.notify_o(), // non mandatory, depends on trigger request
                .addr_to_compress_i       (addr_to_compress[0]),
                .valid_o                  (packet_valid[0]),
                .packet_format_o          (packet_format[0]),
                .packet_f_sync_subformat_o(packet_f_sync_subformat[0]),
                //.packet_f_opt_ext_subformat_o(packet_f_opt_ext_subformat), // non mandatory
                .thaddr_o                 (thaddr[0]),
                .lc_tc_mux_o              (lc_tc_mux[0]),
                .resync_timer_rst_o       (resync_rst),
                .qual_status_o            (qual_status[0]),
                .tc_resync_o              (tc_resync[0]),
                .nc_exc_only_o            (nc_exc_only[0]),
                .nc_ppccd_br_o            (nc_ppccd_br[0]),
                .keep_bits_o              (keep_bits[0])
            );

            /* PACKET EMITTER */
            te_packet_emitter i_te_packet_emitter(
                .clk_i                    (clk_gated),
                .rst_ni                   (rst_ni),
                .valid_i                  (packet_valid[0]),
                .packet_format_i          (packet_format[0]),
                .packet_f_sync_subformat_i(packet_f_sync_subformat[0]),
                //.packet_f_opt_ext_subformat_i(packet_f_opt_ext_subformat), // non mandatory
                .lc_cause_i               (lc_cause),
                .lc_tval_i                (lc_tval),
                .lc_interrupt_i           (lc_interrupt),
                .tc_cause_i               (tc_cause),
                .tc_tval_i                (tc_tval),
                .tc_interrupt_i           (tc_interrupt),
                .tc_resync_i              (tc_resync[0]),
                .nc_exc_only_i            (nc_exc_only[0]),
                .nc_ppccd_br_i            (nc_ppccd_br[0]),
                .nocontext_i              (nocontext),
                .notime_i                 (notime),
                .tc_branch_i              (branch_q),
                .tc_branch_taken_i        (branch_taken_q),
                .tc_priv_i                (tc_priv),
                .tc_time_i                (tc_time), // non mandatory
                //.context_i(), // non mandatory
                .tc_address_i             (tc_address[0]),
                .lc_tc_mux_i              (lc_tc_mux[0]),
                .thaddr_i                 (thaddr[0]),
                .tc_tvec_i                (tc_tvec),
                .lc_epc_i                 (lc_epc),
                .tc_ienable_i             (trace_enable),
                .encoder_mode_i           (encoder_mode),
                .qual_status_i            (qual_status[0]),
                .ioptions_i               (enc_config_q),
                //.denable_i(), // stand-by
                //.dloss_i(), //stand-by
                //.notify_i(), // non mandatory
                .lc_updiscon_i            (lc_updiscon[0]),
                //.irreport_i(), // non mandatory
                //.irdepth_i(), // non mandatory
                .branches_i               (branch_count),
                .branch_map_i             (branch_map),
                .keep_bits_i              (keep_bits[0]),
                .shallow_trace_i          (shallow_trace),
                .packet_valid_o           (packet_emitted[0]),
                .packet_type_o            (packet_type_o[0]),
                .packet_payload_o         (packet_payload_o[0]),
                .payload_length_o         (packet_length_o[0]),
                .branch_map_flush_o       (nc_branch_map_flush),
                .addr_to_compress_o       (addr_to_compress[0])
            );

        end else if (N > 1 && !ONLY_BRANCHES) begin
            // N instances for N > 1 && !ONLY_BRANCHES
            for (genvar i = 0; i < N; i++) begin
                if (i == 0) begin
                    /* PRIORITY */
                    te_priority i_te_priority(
                        .clk_i                    (clk_gated),
                        .rst_ni                   (rst_ni),
                        .valid_i                  (|valid0_q || (enc_activated_q || enc_deactivated_q)),
                        .lc_exception_i           (lc_exception || lc_interrupt),
                        .lc_updiscon_i            (lc_updiscon[i]),
                        .tc_qualified_i           (tc_qualified[i]),
                        .tc_exception_i           (tc_exception|| tc_interrupt),
                        .tc_retired_i             (tc_iretired[i]),
                        .tc_first_qualified_i     (tc_first_qualified),
                        .tc_privchange_i          (privchange_q),
                        //.tc_context_change_i(), // non mandatory
                        //.tc_precise_context_report_i(), // requires ctype signal CPU side
                        //.tc_context_report_as_disc_i(), // ibidem
                        //.tc_imprecise_context_report_i(), // ibidem
                        .tc_gt_max_resync_i       (gt_max_resync_q), // connected only to the first port
                        .tc_et_max_resync_i       (et_max_resync_q), // connected only to the first port
                        .tc_branch_map_empty_i    (tc_branch_map_empty),
                        .tc_branch_map_full_i     (branch_map_full_q), // connected only to the first port
                        //.tc_branch_misprediction_i(), // non mandatory
                        //.tc_pbc_i(), // non mandatory
                        .tc_enc_enabled_i         (enc_activated_q),
                        .tc_enc_disabled_i        (enc_deactivated_q),
                        .tc_opmode_change_i       (enc_config_change_q),
                        .tc_final_qualified_i     (tc_final_qualified),
                        .tc_packets_lost_i        (~encapsulator_ready_i), // non mandatory
                        .nc_exception_i           (nc_exception || nc_interrupt),
                        .nc_privchange_i          (privchange_d),
                        //.nc_context_change_i(),
                        //.nc_precise_context_report_i(), // requires ctype signal CPU side
                        //.nc_context_report_as_disc_i(), // ibidem
                        .nc_branch_map_empty_i    (nc_branch_map_empty),
                        .nc_qualified_i           (nc_qualified[i]),
                        .nc_retired_i             (nc_iretired[i]),
                        //.halted_i(), // non mandatory side band signal
                        //.reset_i(), // ibidem
                        //.implicit_return_i(), // non mandatory
                        //.tc_trigger_req_i(), // non mandatory
                        //.notify_o(), // non mandatory, depends on trigger request
                        .addr_to_compress_i       (addr_to_compress[i]),
                        .valid_o                  (packet_valid[i]),
                        .packet_format_o          (packet_format[i]),
                        .packet_f_sync_subformat_o(packet_f_sync_subformat[i]),
                        //.packet_f_opt_ext_subformat_o(packet_f_opt_ext_subformat), // non mandatory
                        .thaddr_o                 (thaddr[i]),
                        .lc_tc_mux_o              (lc_tc_mux[i]),
                        .resync_timer_rst_o       (resync_rst),
                        .qual_status_o            (qual_status[i]),
                        .tc_resync_o              (tc_resync[i]),
                        .nc_exc_only_o            (nc_exc_only[i]),
                        .nc_ppccd_br_o            (nc_ppccd_br[i]),
                        .keep_bits_o              (keep_bits[i])
                    );

                    /* PACKET EMITTER */
                    te_packet_emitter i_te_packet_emitter(
                        .clk_i                    (clk_gated),
                        .rst_ni                   (rst_ni),
                        .valid_i                  (packet_valid[i]),
                        .packet_format_i          (packet_format[i]),
                        .packet_f_sync_subformat_i(packet_f_sync_subformat[i]),
                        //.packet_f_opt_ext_subformat_i(packet_f_opt_ext_subformat), // non mandatory
                        .lc_cause_i               (lc_cause),
                        .lc_tval_i                (lc_tval),
                        .lc_interrupt_i           (lc_interrupt),
                        .tc_cause_i               (tc_cause),
                        .tc_tval_i                (tc_tval),
                        .tc_interrupt_i           (tc_interrupt),
                        .tc_resync_i              (tc_resync[i]),
                        .nc_exc_only_i            (nc_exc_only[i]),
                        .nc_ppccd_br_i            (nc_ppccd_br[i]),
                        .nocontext_i              (nocontext),
                        .notime_i                 (notime),
                        .tc_branch_i              (branch_q),
                        .tc_branch_taken_i        (branch_taken_q),
                        .tc_priv_i                (tc_priv),
                        .tc_time_i                (tc_time), // non mandatory
                        //.context_i(), // non mandatory
                        .tc_address_i             (tc_address[i]),
                        .lc_tc_mux_i              (lc_tc_mux[i]),
                        .thaddr_i                 (thaddr[i]),
                        .tc_tvec_i                (tc_tvec),
                        .lc_epc_i                 (lc_epc),
                        .tc_ienable_i             (trace_enable),
                        .encoder_mode_i           (encoder_mode),
                        .qual_status_i            (qual_status[i]),
                        .ioptions_i               (enc_config_q),
                        //.denable_i(), // stand-by
                        //.dloss_i(), //stand-by
                        //.notify_i(), // non mandatory
                        .lc_updiscon_i            (lc_updiscon[i]),
                        //.irreport_i(), // non mandatory
                        //.irdepth_i(), // non mandatory
                        .branches_i               (branch_count),
                        .branch_map_i             (branch_map),
                        .keep_bits_i              (keep_bits[i]),
                        .shallow_trace_i          (shallow_trace),
                        .packet_valid_o           (packet_emitted[i]),
                        .packet_type_o            (packet_type_o[i]),
                        .packet_payload_o         (packet_payload_o[i]),
                        .payload_length_o         (packet_length_o[i]),
                        .branch_map_flush_o       (nc_branch_map_flush),
                        .addr_to_compress_o       (addr_to_compress[i])
                    );
                end else begin
                    /* PRIORITY */
                    te_priority i_te_priority(
                        .clk_i                    (clk_gated),
                        .rst_ni                   (rst_ni),
                        .valid_i                  (|valid0_q || (enc_activated_q || enc_deactivated_q)),
                        .lc_exception_i           (lc_exception || lc_interrupt),
                        .lc_updiscon_i            (lc_updiscon[i]),
                        .tc_qualified_i           (tc_qualified[i]),
                        .tc_exception_i           (tc_exception || tc_interrupt),
                        .tc_retired_i             (tc_iretired[i]),
                        .tc_first_qualified_i     (tc_first_qualified),
                        .tc_privchange_i          (privchange_q),
                        //.tc_context_change_i(), // non mandatory
                        //.tc_precise_context_report_i(), // requires ctype signal CPU side
                        //.tc_context_report_as_disc_i(), // ibidem
                        //.tc_imprecise_context_report_i(), // ibidem
                        .tc_gt_max_resync_i       (), // connected only to the first port
                        .tc_et_max_resync_i       (), // connected only to the first port
                        .tc_branch_map_empty_i    (tc_branch_map_empty),
                        .tc_branch_map_full_i     (), // connected only to the first port
                        //.tc_branch_misprediction_i(), // non mandatory
                        //.tc_pbc_i(), // non mandatory
                        .tc_enc_enabled_i         (enc_activated_q),
                        .tc_enc_disabled_i        (enc_deactivated_q),
                        .tc_opmode_change_i       (enc_config_change_q),
                        .tc_final_qualified_i     (tc_final_qualified),
                        .tc_packets_lost_i        (~encapsulator_ready_i), // non mandatory
                        .nc_exception_i           (nc_exception || nc_interrupt),
                        .nc_privchange_i          (privchange_d),
                        //.nc_context_change_i(),
                        //.nc_precise_context_report_i(), // requires ctype signal CPU side
                        //.nc_context_report_as_disc_i(), // ibidem
                        .nc_branch_map_empty_i    (nc_branch_map_empty),
                        .nc_qualified_i           (nc_qualified[i]),
                        .nc_retired_i             (nc_iretired[i]),
                        //.halted_i(), // non mandatory side band signal
                        //.reset_i(), // ibidem
                        //.implicit_return_i(), // non mandatory
                        //.tc_trigger_req_i(), // non mandatory
                        //.notify_o(), // non mandatory, depends on trigger request
                        .addr_to_compress_i       (addr_to_compress[i]),
                        .valid_o                  (packet_valid[i]),
                        .packet_format_o          (packet_format[i]),
                        .packet_f_sync_subformat_o(packet_f_sync_subformat[i]),
                        //.packet_f_opt_ext_subformat_o(packet_f_opt_ext_subformat), // non mandatory
                        .thaddr_o                 (thaddr[i]),
                        .lc_tc_mux_o              (lc_tc_mux[i]),
                        .resync_timer_rst_o       (), // connected only to the first port
                        .qual_status_o            (qual_status[i]),
                        .tc_resync_o              (tc_resync[i]),
                        .nc_exc_only_o            (nc_exc_only[i]),
                        .nc_ppccd_br_o            (nc_ppccd_br[i]),
                        .keep_bits_o              (keep_bits[i])
                    );

                    /* PACKET EMITTER */
                    te_packet_emitter i_te_packet_emitter(
                        .clk_i                    (clk_gated),
                        .rst_ni                   (rst_ni),
                        .valid_i                  (packet_valid[i]),
                        .packet_format_i          (packet_format[i]),
                        .packet_f_sync_subformat_i(packet_f_sync_subformat[i]),
                        //.packet_f_opt_ext_subformat_i(packet_f_opt_ext_subformat), // non mandatory
                        .lc_cause_i               (lc_cause),
                        .lc_tval_i                (lc_tval),
                        .lc_interrupt_i           (lc_interrupt),
                        .tc_cause_i               (tc_cause),
                        .tc_tval_i                (tc_tval),
                        .tc_interrupt_i           (tc_interrupt),
                        .tc_resync_i              (tc_resync[i]),
                        .nc_exc_only_i            (nc_exc_only[i]),
                        .nc_ppccd_br_i            (nc_ppccd_br[i]),
                        .nocontext_i              (nocontext),
                        .notime_i                 (notime),
                        .tc_branch_i              (branch_q),
                        .tc_branch_taken_i        (branch_taken_q),
                        .tc_priv_i                (tc_priv),
                        .tc_time_i                (tc_time), // non mandatory
                        //.context_i(), // non mandatory
                        .tc_address_i             (tc_address[i]),
                        .lc_tc_mux_i              (lc_tc_mux[i]),
                        .thaddr_i                 (thaddr[i]),
                        .tc_tvec_i                (tc_tvec),
                        .lc_epc_i                 (lc_epc),
                        .tc_ienable_i             (trace_enable),
                        .encoder_mode_i           (encoder_mode),
                        .qual_status_i            (qual_status[i]),
                        .ioptions_i               (enc_config_q),
                        //.denable_i(), // stand-by
                        //.dloss_i(), //stand-by
                        //.notify_i(), // non mandatory
                        .lc_updiscon_i            (lc_updiscon[i]),
                        //.irreport_i(), // non mandatory
                        //.irdepth_i(), // non mandatory
                        .branches_i               (branch_count),
                        .branch_map_i             (branch_map),
                        .keep_bits_i              (keep_bits[i]),
                        .shallow_trace_i          (shallow_trace),
                        .packet_valid_o           (packet_emitted[i]),
                        .packet_type_o            (packet_type_o[i]),
                        .packet_payload_o         (packet_payload_o[i]),
                        .payload_length_o         (packet_length_o[i]),
                        .branch_map_flush_o       (), // connected only to the first port
                        .addr_to_compress_o       (addr_to_compress[i])
                    );
                end
            end
        end
    endgenerate

    /* REGISTERS MANAGEMENT */
    always_ff @( posedge clk_i, negedge rst_ni ) begin : registers
        if(~rst_ni) begin
            valid0_q <= '0;
            privchange_q <= '0;
            // context_change_q <= '0;
            //precise_context_report_q <= '0; // requires ctype signal CPU side
            //context_report_as_disc_q <= '0; //ibidem
            //no_context_report_q <= '0; // ibidem
            //imprecise_context_report_q <= '0; // ibidem
            gt_max_resync_q <= '0;
            et_max_resync_q <= '0;
            branch_map_full_q <= '0;
            //branch_misprediction_q <= '0; // non mandatory
            trace_activated_q <= '0;
            enc_activated_q <= '0;
            enc_deactivated_q <= '0;
            //packets_lost_q <= '0; // non mandatory
            enc_config_q <= te_pkg::DELTA_ADDRESS; // 3'b0
            enc_config_change_q <= '0;
            branch_taken_q <= '0;
            branch_q <= '0;
            turn_on_tracer_q <= '0;
        end else begin
            privchange_q <= privchange_d;
            // context_change_q <= context_change_d;
            //precise_context_report_q <= precise_context_report_d; // requires ctype signal CPU side
            //context_report_as_disc_q <= context_report_as_disc_d; //ibidem
            //no_context_report_q <= no_context_report_d; // ibidem
            //imprecise_context_report_q <= imprecise_context_report_d; // ibidem
            branch_q <= branch_d;
            valid0_q <= valid0_d;
            gt_max_resync_q <= gt_max_resync_d;
            et_max_resync_q <= et_max_resync_d;
            branch_map_full_q <= branch_map_full_d;
            //branch_misprediction_q <= branch_misprediction_d; // non mandatory
            trace_activated_q <= trace_activated_d;
            enc_activated_q <= enc_activated_d;
            enc_deactivated_q <= enc_deactivated_d;
            //packets_lost_q <= packets_lost_d; // non mandatory
            enc_config_q <= enc_config_d;
            enc_config_change_q <= enc_config_change_d;
            branch_taken_q <= branch_taken_d;
            turn_on_tracer_q <= turn_on_tracer_d;
        end
    end
    
endmodule