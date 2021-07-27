// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module alsaqr_clk_rst_gen (
    input  logic        ref_clk_i,
    input  logic        test_clk_i,
    input  logic        rstn_glob_i,
    input  logic        rst_dm_i,
    input  logic        test_mode_i,
    input  logic        sel_fll_clk_i,
    input  logic        shift_enable_i,
    FLL_BUS.Slave       soc_fll_slave,
    FLL_BUS.Slave       per_fll_slave,
    FLL_BUS.Slave       cluster_fll_slave,
    output logic        rstn_soc_sync_o,
    output logic        rstn_global_sync_o,
    output logic        rstn_cluster_sync_o,

    output logic        clk_soc_o,
    output logic        clk_per_o,
    output logic        clk_cluster_o
);

    logic s_clk_soc;
    logic s_clk_per;
    logic s_clk_cluster;

    logic s_clk_fll_soc;
    logic s_clk_fll_per;
    logic s_clk_fll_cluster;

    logic s_rstn_soc;

    logic s_rstn_soc_sync;
    logic s_rst_glob_sync;
    logic s_rstn_cluster_sync;


    // currently, FLLs are not supported for FPGA emulation
    `ifndef FPGA_EMUL
    //synopsys translate_off
    freq_meter #(.FLL_NAME("SOC_FLL"),     .MAX_SAMPLE(4096)) SOC_METER (.clk(s_clk_fll_soc));
    freq_meter #(.FLL_NAME("PER_FLL"),     .MAX_SAMPLE(4096)) PER_METER (.clk(s_clk_fll_per));
    freq_meter #(.FLL_NAME("CLUSTER_FLL"), .MAX_SAMPLE(4096)) CLUSTER_METER (.clk(s_clk_fll_cluster));
    //synopsys translate_on

        gf22_FLL i_fll_soc
        (
            .FLLCLK ( s_clk_fll_soc            ),
            .FLLOE  ( 1'b1                     ),
            .REFCLK ( ref_clk_i                ),
            .LOCK   ( soc_fll_slave.lock       ),
            .CFGREQ ( soc_fll_slave.req        ),
            .CFGACK ( soc_fll_slave.ack        ),
            .CFGAD  ( soc_fll_slave.add[1:0]   ),
            .CFGD   ( soc_fll_slave.data       ),
            .CFGQ   ( soc_fll_slave.r_data     ),
            .CFGWEB ( soc_fll_slave.wrn        ),
            .RSTB   ( rstn_glob_i              ),
            .PWD    ( 1'b0                     ),
            .RET    ( 1'b0                     ),
            .TM     ( test_mode_i              ),
            .TE     ( shift_enable_i           ),
            .TD     ( 1'b0                     ), //TO FIX DFT
            .TQ     (                          ), //TO FIX DFT
            .JTD    ( 1'b0                     ), //TO FIX DFT
            .JTQ    (                          )  //TO FIX DFT
        );

        gf22_FLL i_fll_per (
            .FLLCLK ( s_clk_fll_per            ),
            .FLLOE  ( 1'b1                     ),
            .REFCLK ( ref_clk_i                ),
            .LOCK   ( per_fll_slave.lock       ),
            .CFGREQ ( per_fll_slave.req        ),
            .CFGACK ( per_fll_slave.ack        ),
            .CFGAD  ( per_fll_slave.add[1:0]   ),
            .CFGD   ( per_fll_slave.data       ),
            .CFGQ   ( per_fll_slave.r_data     ),
            .CFGWEB ( per_fll_slave.wrn        ),
            .RSTB   ( rstn_glob_i              ),
            .PWD    ( 1'b0                     ),
            .RET    ( 1'b0                     ),
            .TM     ( test_mode_i              ),
            .TE     ( shift_enable_i           ),
            .TD     ( 1'b0                     ), //TO FIX DFT
            .TQ     (                          ), //TO FIX DFT
            .JTD    ( 1'b0                     ), //TO FIX DFT
            .JTQ    (                          )  //TO FIX DFT
        );

        gf22_FLL i_fll_cluster (
            .FLLCLK ( s_clk_fll_cluster            ),
            .FLLOE  ( 1'b1                         ),
            .REFCLK ( ref_clk_i                    ),
            .LOCK   ( cluster_fll_slave.lock       ),
            .CFGREQ ( cluster_fll_slave.req        ),
            .CFGACK ( cluster_fll_slave.ack        ),
            .CFGAD  ( cluster_fll_slave.add[1:0]   ),
            .CFGD   ( cluster_fll_slave.data       ),
            .CFGQ   ( cluster_fll_slave.r_data     ),
            .CFGWEB ( cluster_fll_slave.wrn        ),
            .RSTB   ( rstn_glob_i                  ),
            .PWD    ( 1'b0                         ),
            .RET    ( 1'b0                         ),
            .TM     ( test_mode_i                  ),
            .TE     ( shift_enable_i               ),
            .TD     ( 1'b0                         ), //TO FIX DFT
            .TQ     (                              ), //TO FIX DFT
            .JTD    ( 1'b0                         ), //TO FIX DFT
            .JTQ    (                              )  //TO FIX DFT
        );

    tc_clk_mux2 clk_mux_fll_soc_i (
                .clk0_i    ( s_clk_fll_soc  ),
                .clk1_i    ( ref_clk_i      ),
                .clk_sel_i ( sel_fll_clk_i  ),
                .clk_o     ( s_clk_soc      )
                );

    tc_clk_mux2 clk_mux_fll_per_i (
                .clk0_i    ( s_clk_fll_per  ),
                .clk1_i    ( ref_clk_i      ),
                .clk_sel_i ( sel_fll_clk_i  ),
                .clk_o     ( s_clk_per      )
                );

    tc_clk_mux2 clk_mux_fll_cluster_i (
                .clk0_i    ( s_clk_fll_cluster  ),
                .clk1_i    ( ref_clk_i          ),
                .clk_sel_i ( sel_fll_clk_i      ),
                .clk_o     ( s_clk_cluster      )
                );

     rstgen i_soc_rstgen (
            .clk_i       ( clk_soc_o                ),
            .rst_ni      ( s_rstn_soc & (~rst_dm_i) ),
            .test_mode_i ( test_mode_i              ),
            .rst_no      ( s_rstn_soc_sync          ), //to be used by logic clocked with ref clock in AO domain
            .init_no     (                          )                    //not used
        );

     rstgen i_soc_dm_rstgen (
            .clk_i       ( clk_soc_o                ),
            .rst_ni      ( s_rstn_soc               ),
            .test_mode_i ( test_mode_i              ),
            .rst_no      ( s_rst_glob_sync          ), //to be used by logic clocked with ref clock in AO domain
            .init_no     (                          )                    //not used
        );
   
     rstgen i_cluster_rstgen (
            .clk_i       ( clk_cluster_o       ),
            .rst_ni      ( s_rstn_soc          ),
            .test_mode_i ( test_mode_i         ),
            .rst_no      ( s_rstn_cluster_sync ), //to be used by logic clocked with ref clock in AO domain
            .init_no     (                     )                    //not used
        );

    `else // !`ifndef PULP_FPGA_EMUL

    // Use FPGA dependent clock generation module for both clocks
    // For the FPGA port we remove the clock multiplexers since it doesn't make
    // much sense to clock the circuit directly with the board reference clock
    // (e.g. 200MHz for genesys2 board).

       fpga_clk_gen i_fpga_clk_gen (
                        .ref_clk_i,
                        .rstn_glob_i,
                        .test_mode_i,
                        .shift_enable_i,
                        .soc_clk_o(s_clk_fll_soc),
                        .per_clk_o(s_clk_fll_per),
                        .cluster_clk_o(s_clk_cluster),
                        .soc_cfg_lock_o(soc_fll_slave.lock),
                        .soc_cfg_req_i(soc_fll_slave.req),
                        .soc_cfg_ack_o(soc_fll_slave.ack),
                        .soc_cfg_add_i(soc_fll_slave.add),
                        .soc_cfg_data_i(soc_fll_slave.data),
                        .soc_cfg_r_data_o(soc_fll_slave.r_data),
                        .soc_cfg_wrn_i(soc_fll_slave.wrn),
                        .per_cfg_lock_o(per_fll_slave.lock),
                        .per_cfg_req_i(per_fll_slave.req),
                        .per_cfg_ack_o(per_fll_slave.ack),
                        .per_cfg_add_i(per_fll_slave.add),
                        .per_cfg_data_i(per_fll_slave.data),
                        .per_cfg_r_data_o(per_fll_slave.r_data),
                        .per_cfg_wrn_i(per_fll_slave.wrn),
                        .cluster_cfg_lock_o(cluster_fll_slave.lock),
                        .cluster_cfg_req_i(cluster_fll_slave.req),
                        .cluster_cfg_ack_o(cluster_fll_slave.ack),
                        .cluster_cfg_add_i(cluster_fll_slave.add),
                        .cluster_cfg_data_i(cluster_fll_slave.data),
                        .cluster_cfg_r_data_o(cluster_fll_slave.r_data),
                        .cluster_cfg_wrn_i(cluster_fll_slave.wrn)
                        );

    assign s_clk_soc     = s_clk_fll_soc;
    assign s_clk_cluster = s_clk_fll_cluster;
    assign s_clk_per     = s_clk_fll_per;

    assign s_rstn_soc_sync = s_rstn_soc;
    assign s_rstn_cluster_sync = s_rstn_soc;
    assign s_rst_glob_sync = s_rstn_soc;    

    `endif



    assign s_rstn_soc = rstn_glob_i;
   
    assign clk_soc_o       = s_clk_soc;
    assign clk_per_o       = s_clk_per;
    assign clk_cluster_o   = s_clk_cluster;

    assign rstn_soc_sync_o = s_rstn_soc_sync;
    assign rstn_global_sync_o = s_rst_glob_sync;   
    assign rstn_cluster_sync_o = s_rstn_cluster_sync;

    `ifdef DO_NOT_USE_FLL
        assert property (
            @(posedge clk) (soc_fll_slave_req_i == 1'b0 && per_fll_slave_req_i == 1'b0)  ) else $display("There should be no FLL request (%t)", $time);
    `endif


endmodule
