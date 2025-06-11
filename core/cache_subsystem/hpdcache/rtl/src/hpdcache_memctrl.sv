/*
 *  Copyright 2023 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : April, 2021
 *  Description   : HPDcache Directory and Data Memory RAMs Controller
 *  History       :
 */
module hpdcache_memctrl
import hpdcache_pkg::*;
    //  Parameters
    //  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_word_t = logic,
    parameter type hpdcache_way_vector_t = logic,
    parameter type hpdcache_dir_entry_t = logic,

    parameter type hpdcache_data_word_t = logic,
    parameter type hpdcache_data_be_t = logic,

    parameter type hpdcache_req_data_t = logic,
    parameter type hpdcache_req_be_t = logic,

    parameter type hpdcache_access_data_t = logic,
    parameter type hpdcache_access_be_t = logic
)
    //  }}}

    //  Ports
    //  {{{
(
    //      Global clock and reset signals
    //      {{{
    input  logic                                clk_i,
    input  logic                                rst_ni,
    //      }}}

    //      Global control signals
    //      {{{
    output logic                                ready_o,
    //      }}}

    //      DIR array access interface
    //      {{{
    input  logic                                dir_match_i,
    input  hpdcache_set_t                       dir_match_set_i,
    input  hpdcache_tag_t                       dir_match_tag_i,
    input  logic                                dir_updt_sel_victim_i,
    output hpdcache_way_vector_t                dir_hit_way_o,
    output hpdcache_tag_t                       dir_hit_tag_o,
    output logic                                dir_hit_wback_o,
    output logic                                dir_hit_dirty_o,
    output logic                                dir_hit_fetch_o,

    input  logic                                dir_updt_i,
    input  hpdcache_set_t                       dir_updt_set_i,
    input  hpdcache_way_vector_t                dir_updt_way_i,
    input  hpdcache_tag_t                       dir_updt_tag_i,
    input  logic                                dir_updt_valid_i,
    input  logic                                dir_updt_wback_i,
    input  logic                                dir_updt_dirty_i,
    input  logic                                dir_updt_fetch_i,

    input  logic                                dir_amo_match_i,
    input  hpdcache_set_t                       dir_amo_match_set_i,
    input  hpdcache_tag_t                       dir_amo_match_tag_i,
    input  logic                                dir_amo_updt_sel_victim_i,
    output hpdcache_way_vector_t                dir_amo_hit_way_o,

    input  logic                                dir_refill_i,
    input  hpdcache_set_t                       dir_refill_set_i,
    input  hpdcache_way_vector_t                dir_refill_way_i,
    input  hpdcache_dir_entry_t                 dir_refill_entry_i,
    input  logic                                dir_refill_updt_sel_victim_i,

    input  logic                                dir_victim_sel_i,
    input  hpdcache_set_t                       dir_victim_set_i,
    output logic                                dir_victim_valid_o,
    output logic                                dir_victim_wback_o,
    output logic                                dir_victim_dirty_o,
    output hpdcache_tag_t                       dir_victim_tag_o,
    output hpdcache_way_vector_t                dir_victim_way_o,

    input  logic                                dir_inval_check_i,
    input  hpdcache_nline_t                     dir_inval_nline_i,
    input  logic                                dir_inval_write_i,
    output logic                                dir_inval_hit_o,

    input  logic                                dir_cmo_check_nline_i,
    input  hpdcache_set_t                       dir_cmo_check_nline_set_i,
    input  hpdcache_tag_t                       dir_cmo_check_nline_tag_i,
    output hpdcache_way_vector_t                dir_cmo_check_nline_hit_way_o,
    output logic                                dir_cmo_check_nline_wback_o,
    output logic                                dir_cmo_check_nline_dirty_o,

    input  logic                                dir_cmo_check_entry_i,
    input  hpdcache_set_t                       dir_cmo_check_entry_set_i,
    input  hpdcache_way_vector_t                dir_cmo_check_entry_way_i,
    output logic                                dir_cmo_check_entry_valid_o,
    output logic                                dir_cmo_check_entry_wback_o,
    output logic                                dir_cmo_check_entry_dirty_o,
    output hpdcache_tag_t                       dir_cmo_check_entry_tag_o,

    input  logic                                dir_cmo_updt_i,
    input  hpdcache_set_t                       dir_cmo_updt_set_i,
    input  hpdcache_way_vector_t                dir_cmo_updt_way_i,
    input  hpdcache_tag_t                       dir_cmo_updt_tag_i,
    input  logic                                dir_cmo_updt_valid_i,
    input  logic                                dir_cmo_updt_wback_i,
    input  logic                                dir_cmo_updt_dirty_i,
    input  logic                                dir_cmo_updt_fetch_i,
    //      }}}

    //      DATA array access interface
    //      {{{
    input  logic                                data_req_read_i,
    input  hpdcache_set_t                       data_req_read_set_i,
    input  hpdcache_req_size_t                  data_req_read_size_i,
    input  hpdcache_word_t                      data_req_read_word_i,
    output hpdcache_req_data_t                  data_req_read_data_o,

    input  logic                                data_req_write_i,
    input  logic                                data_req_write_enable_i,
    input  hpdcache_set_t                       data_req_write_set_i,
    input  hpdcache_req_size_t                  data_req_write_size_i,
    input  hpdcache_word_t                      data_req_write_word_i,
    input  hpdcache_req_data_t                  data_req_write_data_i,
    input  hpdcache_req_be_t                    data_req_write_be_i,

    input  logic                                data_amo_write_i,
    input  logic                                data_amo_write_enable_i,
    input  hpdcache_set_t                       data_amo_write_set_i,
    input  hpdcache_req_size_t                  data_amo_write_size_i,
    input  hpdcache_word_t                      data_amo_write_word_i,
    input  hpdcache_req_data_t                  data_amo_write_data_i,
    input  hpdcache_req_be_t                    data_amo_write_be_i,

    input  logic                                data_flush_read_i,
    input  hpdcache_set_t                       data_flush_read_set_i,
    input  hpdcache_word_t                      data_flush_read_word_i,
    input  hpdcache_way_vector_t                data_flush_read_way_i,
    output hpdcache_access_data_t               data_flush_read_data_o,

    input  logic                                data_refill_i,
    input  hpdcache_set_t                       data_refill_set_i,
    input  hpdcache_way_vector_t                data_refill_way_i,
    input  hpdcache_word_t                      data_refill_word_i,
    input  hpdcache_access_data_t               data_refill_data_i
    //      }}}
);
    //  }}}

    //  Definition of constants and types
    //  {{{
    localparam int unsigned HPDCACHE_DIR_RAM_WIDTH = $bits(hpdcache_dir_entry_t);
    localparam int unsigned HPDCACHE_DIR_RAM_ADDR_WIDTH = $clog2(HPDcacheCfg.u.sets);
    localparam int unsigned HPDCACHE_DATA_RAM_ENTR_PER_SET = HPDcacheCfg.u.clWords/
                                                             HPDcacheCfg.u.accessWords;
    localparam int unsigned HPDCACHE_DATA_RAM_DEPTH = HPDcacheCfg.u.sets*
                                                      HPDCACHE_DATA_RAM_ENTR_PER_SET;
    localparam int unsigned HPDCACHE_DATA_RAM_WIDTH = HPDcacheCfg.u.dataWaysPerRamWord*
                                                      HPDcacheCfg.u.wordWidth;
    localparam int unsigned HPDCACHE_DATA_RAM_ADDR_WIDTH = $clog2(HPDCACHE_DATA_RAM_DEPTH);
    localparam int unsigned HPDCACHE_DATA_REQ_RATIO = HPDcacheCfg.u.accessWords/
                                                      HPDcacheCfg.u.reqWords;
    localparam int unsigned HPDCACHE_DATA_RAM_Y_CUTS = HPDcacheCfg.u.ways/
                                                       HPDcacheCfg.u.dataWaysPerRamWord;
    localparam int unsigned HPDCACHE_DATA_RAM_X_CUTS = HPDcacheCfg.u.accessWords;
    localparam int unsigned HPDCACHE_ALL_CUTS = HPDCACHE_DATA_RAM_X_CUTS*HPDCACHE_DATA_RAM_Y_CUTS;

    typedef logic [HPDCACHE_DIR_RAM_ADDR_WIDTH-1:0] hpdcache_dir_addr_t;

    typedef logic [HPDCACHE_DATA_RAM_ADDR_WIDTH-1:0] hpdcache_data_ram_addr_t;
    typedef hpdcache_data_word_t[HPDcacheCfg.u.dataWaysPerRamWord-1:0] hpdcache_data_ram_data_t;
    typedef hpdcache_data_be_t  [HPDcacheCfg.u.dataWaysPerRamWord-1:0] hpdcache_data_ram_be_t;
    typedef logic [HPDCACHE_DATA_RAM_Y_CUTS-1:0] hpdcache_data_ram_row_idx_t;
    typedef logic [$clog2(HPDcacheCfg.u.dataWaysPerRamWord)-1:0] hpdcache_data_ram_way_idx_t;
    typedef logic [HPDCACHE_DATA_RAM_X_CUTS-1:0] hpdcache_data_row_enable_t;
    typedef hpdcache_data_row_enable_t [HPDCACHE_DATA_RAM_Y_CUTS-1:0] hpdcache_data_enable_t;

    typedef hpdcache_data_ram_data_t
          [HPDCACHE_DATA_RAM_Y_CUTS-1:0]
          [HPDCACHE_DATA_RAM_X_CUTS-1:0]
          hpdcache_data_entry_t;
    typedef hpdcache_data_ram_data_t
          [HPDCACHE_DATA_RAM_X_CUTS-1:0]
          hpdcache_data_row_t;
    typedef hpdcache_data_ram_be_t
          [HPDCACHE_DATA_RAM_Y_CUTS-1:0]
          [HPDCACHE_DATA_RAM_X_CUTS-1:0]
          hpdcache_data_be_entry_t;
    typedef hpdcache_data_ram_addr_t
          [HPDCACHE_DATA_RAM_Y_CUTS-1:0]
          [HPDCACHE_DATA_RAM_X_CUTS-1:0]
          hpdcache_data_addr_t;
    //  }}}

    //  Definition of functions
    //  {{{

    //      hpdcache_compute_data_ram_cs
    //
    //      description: This function computes the chip-select signal for data
    //                   RAMs depending on the request size and the word offset
    function automatic hpdcache_data_row_enable_t hpdcache_compute_data_ram_cs(
            input hpdcache_req_size_t size_i,
            input hpdcache_word_t     word_i);

        localparam hpdcache_uint32 OffWidth =
                HPDcacheCfg.u.accessWords > 1 ? $clog2(HPDcacheCfg.u.accessWords) : 1;

        hpdcache_data_row_enable_t ret;
        hpdcache_uint32 off;

        case (size_i)
            3'h0,
            3'h1,
            3'h2,
            3'h3:    ret = hpdcache_data_row_enable_t'({ 64/HPDcacheCfg.u.wordWidth{1'b1}});
            3'h4:    ret = hpdcache_data_row_enable_t'({128/HPDcacheCfg.u.wordWidth{1'b1}});
            3'h5:    ret = hpdcache_data_row_enable_t'({256/HPDcacheCfg.u.wordWidth{1'b1}});
            default: ret = hpdcache_data_row_enable_t'({512/HPDcacheCfg.u.wordWidth{1'b1}});
        endcase

        off = HPDcacheCfg.u.accessWords > 1 ? hpdcache_uint'(word_i[0 +: OffWidth]) : 0;
        return hpdcache_data_row_enable_t'(ret << off);
    endfunction

    function automatic hpdcache_data_ram_row_idx_t hpdcache_way_to_data_ram_row(
        input hpdcache_way_vector_t way);
        hpdcache_data_ram_row_idx_t ret;
        for (hpdcache_uint i = 0; i < HPDCACHE_DATA_RAM_Y_CUTS; i++) begin
            ret[i] = |way[i*HPDcacheCfg.u.dataWaysPerRamWord +: HPDcacheCfg.u.dataWaysPerRamWord];
        end
        return ret;
    endfunction

    function automatic hpdcache_data_ram_way_idx_t hpdcache_way_to_data_ram_word(
            input hpdcache_way_vector_t way);
        for (hpdcache_uint i = 0; i < HPDcacheCfg.u.ways; i++) begin
            if (way[i]) return hpdcache_data_ram_way_idx_t'(i % HPDcacheCfg.u.dataWaysPerRamWord);
        end
        return 0;
    endfunction

    function automatic hpdcache_data_ram_addr_t hpdcache_set_to_data_ram_addr(
            input hpdcache_set_t set,
            input hpdcache_word_t word);
        hpdcache_uint ret;

        ret = (hpdcache_uint'(set)*(HPDcacheCfg.u.clWords / HPDcacheCfg.u.accessWords)) +
              (hpdcache_uint'(word) / HPDcacheCfg.u.accessWords);

        return hpdcache_data_ram_addr_t'(ret);
    endfunction
    //  }}}

    //  Definition of internal signals and registers
    //  {{{
    genvar gen_i, gen_j, gen_k;

    //      Directory initialization signals and registers
    logic                                      init_q,     init_d;
    hpdcache_dir_addr_t                        init_set_q, init_set_d;
    hpdcache_way_vector_t                      init_dir_cs;

    //      Directory valid bit vector (one bit per set and way)
    hpdcache_set_t                                dir_req_set_q;
    hpdcache_way_vector_t                         dir_req_way_q;
    hpdcache_dir_addr_t                           dir_addr;
    hpdcache_way_vector_t                         dir_cs;
    hpdcache_way_vector_t                         dir_we;
    hpdcache_dir_entry_t [HPDcacheCfg.u.ways-1:0] dir_wentry;
    hpdcache_dir_entry_t [HPDcacheCfg.u.ways-1:0] dir_rentry;
    logic                [HPDcacheCfg.u.ways-1:0] dir_valid;
    logic                [HPDcacheCfg.u.ways-1:0] dir_wback;
    logic                [HPDcacheCfg.u.ways-1:0] dir_dirty;
    logic                [HPDcacheCfg.u.ways-1:0] dir_fetch;

    hpdcache_data_addr_t                       data_addr;
    hpdcache_data_enable_t                     data_cs;
    hpdcache_data_enable_t                     data_we;
    hpdcache_data_be_entry_t                   data_wbyteenable;
    hpdcache_data_entry_t                      data_wentry;
    hpdcache_data_entry_t                      data_rentry;

    logic                                      data_write;
    logic                                      data_write_enable;
    hpdcache_set_t                             data_write_set;
    hpdcache_req_size_t                        data_write_size;
    hpdcache_word_t                            data_write_word;
    hpdcache_access_data_t                     data_write_data;
    hpdcache_access_be_t                       data_write_be;

    hpdcache_access_data_t                     data_req_write_data;
    hpdcache_access_be_t                       data_req_write_be;

    hpdcache_access_data_t                     data_amo_write_data;
    hpdcache_access_be_t                       data_amo_write_be;

    hpdcache_way_vector_t                      data_way;

    hpdcache_data_ram_row_idx_t                data_ram_row;
    hpdcache_data_ram_way_idx_t                data_ram_word;

    hpdcache_tag_t                             dir_inval_tag;
    hpdcache_set_t                             dir_inval_set;
    hpdcache_way_vector_t                      dir_inval_hit_way;
    //  }}}

    //  Init FSM
    //  {{{
    always_comb
    begin : init_comb
        init_dir_cs = '0;
        init_d      = init_q;
        init_set_d  = init_set_q;

        unique case (init_q)
            1'b0: begin
                init_d      = (hpdcache_uint'(init_set_q) == (HPDcacheCfg.u.sets - 1));
                init_set_d  = init_set_q + 1;
                init_dir_cs = '1;
            end

            1'b1: begin
                init_d      = 1'b1;
                init_set_d  = init_set_q;
            end
        endcase
    end

    assign ready_o = init_q;

    always_ff @(posedge clk_i or negedge rst_ni)
    begin : init_ff
        if (!rst_ni) begin
            init_q      <= 1'b0;
            init_set_q  <= 0;
        end else begin
            init_q      <= init_d;
            init_set_q  <= init_set_d;
        end
    end
    //  }}}

    //  Memory arrays
    //  {{{
    generate
        genvar x, y, dir_w;

        //  Directory
        //
        for (dir_w = 0; dir_w < int'(HPDcacheCfg.u.ways); dir_w++) begin : gen_dir_sram
            hpdcache_sram #(
                .DATA_SIZE (HPDCACHE_DIR_RAM_WIDTH),
                .ADDR_SIZE (HPDCACHE_DIR_RAM_ADDR_WIDTH)
            ) dir_sram (
                .clk       (clk_i),
                .rst_n     (rst_ni),
                .cs        (dir_cs[dir_w]),
                .we        (dir_we[dir_w]),
                .addr      (dir_addr),
                .wdata     (dir_wentry[dir_w]),
                .rdata     (dir_rentry[dir_w])
            );
        end

        //  Data
        //
        for (y = 0; y < int'(HPDCACHE_DATA_RAM_Y_CUTS); y++) begin : gen_data_sram_row
            for (x = 0; x < int'(HPDCACHE_DATA_RAM_X_CUTS); x++) begin : gen_data_sram_col
                if (HPDcacheCfg.u.dataRamByteEnable) begin : gen_data_sram_wbyteenable
                    hpdcache_sram_wbyteenable #(
                        .DATA_SIZE   (HPDCACHE_DATA_RAM_WIDTH),
                        .ADDR_SIZE   (HPDCACHE_DATA_RAM_ADDR_WIDTH)
                    ) data_sram (
                        .clk         (clk_i),
                        .rst_n       (rst_ni),
                        .cs          (data_cs[y][x]),
                        .we          (data_we[y][x]),
                        .addr        (data_addr[y][x]),
                        .wdata       (data_wentry[y][x]),
                        .wbyteenable (data_wbyteenable[y][x]),
                        .rdata       (data_rentry[y][x])
                    );
                end else begin : gen_data_sram_wmask
                    hpdcache_data_ram_data_t data_wmask;

                    //  build the bitmask from the write byte enable signal
                    always_comb
                    begin : data_wmask_comb
                        for (int w = 0; w < HPDcacheCfg.u.dataWaysPerRamWord; w++) begin
                            for (int b = 0; b < HPDcacheCfg.u.wordWidth/8; b++) begin
                                data_wmask[w][8*b +: 8] = {8{data_wbyteenable[y][x][w][b]}};
                            end
                        end
                    end

                    hpdcache_sram_wmask #(
                        .DATA_SIZE   (HPDCACHE_DATA_RAM_WIDTH),
                        .ADDR_SIZE   (HPDCACHE_DATA_RAM_ADDR_WIDTH)
                    ) data_sram (
                        .clk         (clk_i),
                        .rst_n       (rst_ni),
                        .cs          (data_cs[y][x]),
                        .we          (data_we[y][x]),
                        .addr        (data_addr[y][x]),
                        .wdata       (data_wentry[y][x]),
                        .wmask       (data_wmask),
                        .rdata       (data_rentry[y][x])
                    );
                end
            end
        end
    endgenerate
    //  }}}

    //  Directory RAM request mux
    //  {{{
    assign dir_inval_set = dir_inval_nline_i[0 +: HPDcacheCfg.setWidth];
    assign dir_inval_tag = dir_inval_nline_i[HPDcacheCfg.setWidth +: HPDcacheCfg.tagWidth];

    always_comb
    begin : dir_ctrl_comb
        unique case (1'b1)
            //  Cache directory initialization
            ~init_q: begin
                dir_addr    = init_set_q;
                dir_cs      = init_dir_cs;
                dir_we      = '1;
                dir_wentry  = '0;
            end

            //  Cache directory match tag -> hit
            dir_match_i: begin
                dir_addr    = dir_match_set_i;
                dir_cs      = '1;
                dir_we      = '0;
                dir_wentry  = '0;
            end

            //  Cache directory AMO match tag -> hit
            dir_amo_match_i: begin
                dir_addr    = dir_amo_match_set_i;
                dir_cs      = '1;
                dir_we      = '0;
                dir_wentry  = '0;
            end

            //  Cache directory update
            dir_refill_i: begin
                dir_addr    = dir_refill_set_i;
                dir_cs      = dir_refill_way_i;
                dir_we      = dir_refill_way_i;
                dir_wentry  = {HPDcacheCfg.u.ways{dir_refill_entry_i}};
            end

            //  Cache directory invalidate check from the NoC
            dir_inval_check_i: begin
                dir_addr    = dir_inval_set;
                dir_cs      = '1;
                dir_we      = '0;
                dir_wentry  = '0;
            end

            //  Cache directory invalidate from the NoC
            dir_inval_write_i: begin
                dir_addr    = dir_inval_set;
                dir_cs      = dir_inval_hit_way;
                dir_we      = dir_inval_hit_way;
                dir_wentry  = '0;
            end

            //  Cache directory CMO match tag
            dir_cmo_check_nline_i: begin
                dir_addr    = dir_cmo_check_nline_set_i;
                dir_cs      = '1;
                dir_we      = '0;
                dir_wentry  = '0;
            end

            //  Cache directory CMO match tag
            dir_cmo_check_entry_i: begin
                dir_addr    = dir_cmo_check_entry_set_i;
                dir_cs      = dir_cmo_check_entry_way_i;
                dir_we      = '0;
                dir_wentry  = '0;
            end

            //  Cache directory CMO inval tag
            dir_cmo_updt_i: begin
                dir_addr    = dir_cmo_updt_set_i;
                dir_cs      = dir_cmo_updt_way_i;
                dir_we      = dir_cmo_updt_way_i;

                for (hpdcache_uint i = 0; i < HPDcacheCfg.u.ways; i++) begin
                    dir_wentry[i] = '{
                        valid: dir_cmo_updt_valid_i,
                        wback: dir_cmo_updt_wback_i,
                        dirty: dir_cmo_updt_dirty_i,
                        fetch: dir_cmo_updt_fetch_i,
                        tag  : dir_cmo_updt_tag_i
                    };
                end
            end

            //  Cache directory match tag -> hit
            dir_updt_i: begin
                dir_addr    = dir_updt_set_i;
                dir_cs      = dir_updt_way_i;
                dir_we      = dir_updt_way_i;

                for (hpdcache_uint i = 0; i < HPDcacheCfg.u.ways; i++) begin
                    dir_wentry[i] = '{
                        valid: dir_updt_valid_i,
                        wback: dir_updt_wback_i,
                        dirty: dir_updt_dirty_i,
                        fetch: dir_updt_fetch_i,
                        tag  : dir_updt_tag_i
                    };
                end
            end

            //  Do nothing
            default: begin
                dir_addr    = dir_req_set_q;
                dir_cs      = '0;
                dir_we      = '0;
                dir_wentry  = '0;
            end
        endcase
    end

    //  }}}

    //  Directory hit logic
    //  {{{
    hpdcache_tag_t [HPDcacheCfg.u.ways-1:0] dir_tags;
    hpdcache_way_vector_t req_hit;
    hpdcache_way_vector_t amo_hit;
    hpdcache_way_vector_t cmo_hit;
    hpdcache_way_vector_t inval_hit;

    for (gen_i = 0; gen_i < int'(HPDcacheCfg.u.ways); gen_i++)
    begin : gen_dir_match_tag
        assign dir_tags[gen_i] = dir_rentry[gen_i].tag;

        assign req_hit[gen_i]   = (dir_tags[gen_i] == dir_match_tag_i);
        assign amo_hit[gen_i]   = (dir_tags[gen_i] == dir_amo_match_tag_i);
        assign cmo_hit[gen_i]   = (dir_tags[gen_i] == dir_cmo_check_nline_tag_i);
        assign inval_hit[gen_i] = (dir_tags[gen_i] == dir_inval_tag);

        assign dir_hit_way_o[gen_i]                 = dir_valid[gen_i] & req_hit[gen_i];
        assign dir_amo_hit_way_o[gen_i]             = dir_valid[gen_i] & amo_hit[gen_i];
        assign dir_cmo_check_nline_hit_way_o[gen_i] = dir_valid[gen_i] & cmo_hit[gen_i];
        assign dir_inval_hit_way[gen_i]             = dir_valid[gen_i] & inval_hit[gen_i];
    end

    hpdcache_mux #(
        .NINPUT      (HPDcacheCfg.u.ways),
        .DATA_WIDTH  (HPDcacheCfg.tagWidth),
        .ONE_HOT_SEL (1'b1)
    ) hit_tag_mux_i(
        .data_i      (dir_tags),
        .sel_i       (dir_hit_way_o),
        .data_o      (dir_hit_tag_o)
    );

    assign dir_hit_wback_o = |(dir_hit_way_o & dir_wback);
    assign dir_hit_dirty_o = |(dir_hit_way_o & dir_dirty);
    assign dir_hit_fetch_o = |(dir_hit_way_o & dir_fetch);

    assign dir_cmo_check_nline_wback_o = |(dir_cmo_check_nline_hit_way_o & dir_wback);
    assign dir_cmo_check_nline_dirty_o = |(dir_cmo_check_nline_hit_way_o & dir_dirty);
    assign dir_cmo_check_entry_valid_o = |(dir_req_way_q & dir_valid);
    assign dir_cmo_check_entry_wback_o = |(dir_req_way_q & dir_wback);
    assign dir_cmo_check_entry_dirty_o = |(dir_req_way_q & dir_dirty);
    hpdcache_mux #(
        .NINPUT      (HPDcacheCfg.u.ways),
        .DATA_WIDTH  (HPDcacheCfg.tagWidth),
        .ONE_HOT_SEL (1'b1)
    ) flush_tag_mux_i(
        .data_i      (dir_tags),
        .sel_i       (dir_req_way_q),
        .data_o      (dir_cmo_check_entry_tag_o)
    );

    assign dir_victim_valid_o = |(dir_victim_way_o & dir_valid);
    assign dir_victim_wback_o = |(dir_victim_way_o & dir_wback);
    assign dir_victim_dirty_o = |(dir_victim_way_o & dir_dirty);
    hpdcache_mux #(
        .NINPUT      (HPDcacheCfg.u.ways),
        .DATA_WIDTH  (HPDcacheCfg.tagWidth),
        .ONE_HOT_SEL (1'b1)
    ) victim_tag_mux_i(
        .data_i      (dir_tags),
        .sel_i       (dir_victim_way_o),
        .data_o      (dir_victim_tag_o)
    );

    assign dir_inval_hit_o = |dir_inval_hit_way;
    //  }}}

    //  Directory victim select logic
    //  {{{
    logic                 updt_sel_victim;
    hpdcache_way_vector_t updt_sel_victim_way;
    hpdcache_set_t        updt_sel_victim_set;

    assign updt_sel_victim = dir_updt_sel_victim_i |
                             dir_refill_updt_sel_victim_i |
                             dir_amo_updt_sel_victim_i;

    assign updt_sel_victim_way = dir_updt_sel_victim_i        ? dir_hit_way_o :
                                 dir_refill_updt_sel_victim_i ? dir_refill_way_i :
                                 dir_amo_hit_way_o;

    assign updt_sel_victim_set = dir_refill_updt_sel_victim_i ? dir_refill_set_i :
                                 dir_req_set_q;

    for (gen_i = 0; gen_i < HPDcacheCfg.u.ways; gen_i++) begin : gen_dir_valid_bv
        assign dir_valid[gen_i] = dir_rentry[gen_i].valid;
        assign dir_wback[gen_i] = dir_rentry[gen_i].wback;
        assign dir_dirty[gen_i] = dir_rentry[gen_i].dirty;
        assign dir_fetch[gen_i] = dir_rentry[gen_i].fetch;
    end


    hpdcache_victim_sel #(
        .HPDcacheCfg              (HPDcacheCfg),
        .hpdcache_set_t           (hpdcache_set_t),
        .hpdcache_way_vector_t    (hpdcache_way_vector_t)
    ) victim_sel_i(
        .clk_i,
        .rst_ni,

        .updt_i                   (updt_sel_victim),
        .updt_set_i               (updt_sel_victim_set),
        .updt_way_i               (updt_sel_victim_way),

        .sel_victim_i             (dir_victim_sel_i),
        .sel_dir_valid_i          (dir_valid),
        .sel_dir_wback_i          (dir_wback),
        .sel_dir_dirty_i          (dir_dirty),
        .sel_dir_fetch_i          (dir_fetch),
        .sel_victim_set_i         (dir_victim_set_i),
        .sel_victim_way_o         (dir_victim_way_o)
    );
    //  }}}

    //  Data RAM request multiplexor
    //  {{{

    //  Upsize the request interface to match the maximum access width of the data RAM
    if (HPDCACHE_DATA_REQ_RATIO > 1) begin : gen_upsize_data_req_write
        //  demux request DATA
        assign data_req_write_data = {HPDCACHE_DATA_REQ_RATIO{data_req_write_data_i}};

        //  demux request BE
        hpdcache_demux #(
            .NOUTPUT     (HPDCACHE_DATA_REQ_RATIO),
            .DATA_WIDTH  (HPDcacheCfg.reqDataWidth/8),
            .ONE_HOT_SEL (1'b0)
        ) data_req_write_be_demux_i (
            .data_i      (data_req_write_be_i),
            .sel_i       (data_req_write_word_i[HPDcacheCfg.reqWordIdxWidth +:
                                                $clog2(HPDCACHE_DATA_REQ_RATIO)]),
            .data_o      (data_req_write_be)
        );
    end else begin : gen_eqsize_data_req_write
        assign data_req_write_data = data_req_write_data_i;
        assign data_req_write_be   = data_req_write_be_i;
    end

    //  Upsize the AMO data interface to match the maximum access width of the data RAM
    if (HPDCACHE_DATA_REQ_RATIO > 1) begin : gen_upsize_amo_req_write
        assign data_amo_write_data = {HPDCACHE_DATA_REQ_RATIO{data_amo_write_data_i}};

        hpdcache_demux #(
            .NOUTPUT          (HPDCACHE_DATA_REQ_RATIO),
            .DATA_WIDTH       (HPDcacheCfg.reqDataWidth/8),
            .ONE_HOT_SEL      (1'b0)
        ) amo_be_demux_i(
            .data_i           (data_amo_write_be_i),
            .sel_i            (data_amo_write_word_i[HPDcacheCfg.reqWordIdxWidth +:
                                                     $clog2(HPDCACHE_DATA_REQ_RATIO)]),
            .data_o           (data_amo_write_be)
        );
    end else begin : gen_eqsize_amo_req_write
        assign data_amo_write_data = data_amo_write_data_i;
        assign data_amo_write_be   = data_amo_write_be_i;
    end

    //  Multiplex between data write requests
    always_comb
    begin : data_write_comb
        unique case (1'b1)
            data_refill_i: begin
                data_write        = 1'b1;
                data_write_enable = 1'b1;
                data_write_set    = data_refill_set_i;
                data_write_size   = hpdcache_req_size_t'($clog2(HPDcacheCfg.accessWidth/8));
                data_write_word   = data_refill_word_i;
                data_write_data   = data_refill_data_i;
                data_write_be     = '1;
            end

            data_req_write_i: begin
                data_write        = 1'b1;
                data_write_enable = data_req_write_enable_i;
                data_write_set    = data_req_write_set_i;
                data_write_size   = data_req_write_size_i;
                data_write_word   = data_req_write_word_i;
                data_write_data   = data_req_write_data;
                data_write_be     = data_req_write_be;
            end

            data_amo_write_i: begin
                data_write        = 1'b1;
                data_write_enable = data_amo_write_enable_i;
                data_write_set    = data_amo_write_set_i;
                data_write_size   = data_amo_write_size_i;
                data_write_word   = data_amo_write_word_i;
                data_write_data   = data_amo_write_data;
                data_write_be     = data_amo_write_be;
            end

            default: begin
                data_write        = 1'b0;
                data_write_enable = 1'b0;
                data_write_set    = '0;
                data_write_size   = '0;
                data_write_word   = '0;
                data_write_data   = '0;
                data_write_be     = '0;
            end
        endcase
    end

    //  Multiplex between read and write access on the data RAM
    assign  data_way = data_refill_i     ? data_refill_way_i :
                       data_flush_read_i ? data_flush_read_way_i :
                       data_amo_write_i  ? dir_amo_hit_way_o :
                                           dir_hit_way_o;

    //  Decode way index
    assign data_ram_word = hpdcache_way_to_data_ram_word(data_way);
    assign data_ram_row = hpdcache_way_to_data_ram_row(data_way);

    always_comb
    begin : data_ctrl_comb
        data_addr        = '0;
        data_cs          = '0;
        data_we          = '0;
        data_wbyteenable = '0;
        data_wentry      = '0;

        unique case (1'b1)
            //  Select data read inputs
            data_req_read_i: begin
                data_addr = {HPDCACHE_ALL_CUTS{
                    hpdcache_set_to_data_ram_addr(data_req_read_set_i, data_req_read_word_i)}
                };

                for (int unsigned i = 0; i < HPDCACHE_DATA_RAM_Y_CUTS; i++) begin
                    data_cs[i] = hpdcache_compute_data_ram_cs(data_req_read_size_i,
                                                              data_req_read_word_i);
                end
            end

            //  Select data flush read inputs
            data_flush_read_i: begin
                data_addr = {HPDCACHE_ALL_CUTS{
                    hpdcache_set_to_data_ram_addr(data_flush_read_set_i, data_flush_read_word_i)}
                };
                for (int unsigned i = 0; i < HPDCACHE_DATA_RAM_Y_CUTS; i++) begin
                    data_cs[i] = data_ram_row[i] ? '1 : '0;
                end
            end

            //  Select data write inputs
            data_write: begin
                data_addr = {HPDCACHE_ALL_CUTS{hpdcache_set_to_data_ram_addr(data_write_set,
                                                                             data_write_word)}};

                for (int unsigned i = 0; i < HPDCACHE_DATA_RAM_Y_CUTS; i++) begin
                    for (int unsigned j = 0; j < HPDCACHE_DATA_RAM_X_CUTS; j++) begin
                        data_wentry[i][j] = {HPDcacheCfg.u.dataWaysPerRamWord{data_write_data[j]}};
                    end
                end

                for (int unsigned i = 0; i < HPDCACHE_DATA_RAM_Y_CUTS; i++) begin
                    data_cs[i] = hpdcache_compute_data_ram_cs(data_write_size, data_write_word);

                    if (data_ram_row[i]) begin
                        data_we[i] = data_write_enable ? data_cs[i] : '0;
                    end

                    //  Build the write mask
                    for (int unsigned j = 0; j < HPDcacheCfg.u.accessWords; j++) begin
                        for (int unsigned k = 0; k < HPDcacheCfg.u.dataWaysPerRamWord; k++) begin
                            data_wbyteenable[i][j][k] = (k == hpdcache_uint'(data_ram_word)) ?
                                                        data_write_be[j] : '0;
                        end
                    end
                end
            end

            default: begin
                //  Do nothing
            end
        endcase
    end
    //  }}}

    //  Data RAM read data multiplexor
    //  {{{
    hpdcache_req_data_t [HPDCACHE_DATA_REQ_RATIO-1:0][HPDcacheCfg.u.ways-1:0] data_read_words;
    hpdcache_req_data_t                              [HPDcacheCfg.u.ways-1:0] data_read_req_word;

    //  Organize the read data by words (all ways for the same word are contiguous)
    for (gen_i = 0; gen_i < int'(HPDCACHE_DATA_REQ_RATIO); gen_i++) begin : gen_data_rentry_i
        for (gen_j = 0; gen_j < int'(HPDcacheCfg.u.ways); gen_j++) begin : gen_data_rentry_j
            for (gen_k = 0; gen_k < int'(HPDcacheCfg.u.reqWords); gen_k++) begin : gen_data_rentry_k
                assign data_read_words[gen_i][gen_j][gen_k] =
                        data_rentry[(gen_j / HPDcacheCfg.u.dataWaysPerRamWord)]
                                   [(gen_i * HPDcacheCfg.u.reqWords) + gen_k]
                                   [(gen_j % HPDcacheCfg.u.dataWaysPerRamWord)];
            end
        end
    end

    //  Mux the data according to the access word
    typedef logic [$clog2(HPDCACHE_DATA_REQ_RATIO)-1:0] data_req_word_t;
    if (HPDCACHE_DATA_REQ_RATIO > 1) begin : gen_req_width_lt_ram_width
        data_req_word_t data_read_req_word_index_q;

        hpdcache_mux #(
            .NINPUT      (HPDCACHE_DATA_REQ_RATIO),
            .DATA_WIDTH  (HPDcacheCfg.reqDataWidth*HPDcacheCfg.u.ways)
        ) data_read_req_word_mux_i(
            .data_i      (data_read_words),
            .sel_i       (data_read_req_word_index_q),
            .data_o      (data_read_req_word)
        );

        always_ff @(posedge clk_i)
        begin : data_req_read_word_ff
            data_read_req_word_index_q <=
                    data_req_read_word_i[HPDcacheCfg.reqWordIdxWidth +:
                                         $clog2(HPDCACHE_DATA_REQ_RATIO)];
        end
    end

    //  Request data interface width is equal to the data RAM width
    else begin : gen_req_width_eq_ram_width
        assign data_read_req_word = data_read_words;
    end

    //  Mux the data according to the hit way
    hpdcache_mux #(
        .NINPUT      (HPDcacheCfg.u.ways),
        .DATA_WIDTH  (HPDcacheCfg.reqDataWidth),
        .ONE_HOT_SEL (1'b1)
    ) data_read_req_word_way_mux_i(
        .data_i      (data_read_req_word),
        .sel_i       (dir_hit_way_o),
        .data_o      (data_req_read_data_o)
    );


    //  Delay the accessed set for checking the tag from the directory in the
    //  next cycle (hit logic)
    always_ff @(posedge clk_i)
    begin : req_read_ff
        if (dir_match_i || dir_amo_match_i || dir_cmo_check_nline_i || dir_inval_check_i) begin
            dir_req_set_q <= dir_addr;
        end
        if (dir_cmo_check_entry_i) begin
            dir_req_way_q <= dir_cmo_check_entry_way_i;
        end
    end
    //  }}}

    //  Select flush data
    //  {{{
    hpdcache_data_ram_data_t
        [HPDcacheCfg.u.accessWords-1:0]
        data_flush_row_data;

    hpdcache_data_word_t
        [HPDcacheCfg.u.dataWaysPerRamWord-1:0]
        [HPDcacheCfg.u.accessWords-1:0]
        data_flush_ways_data;

    hpdcache_data_ram_row_idx_t data_flush_row_index_q;
    logic [HPDcacheCfg.u.dataWaysPerRamWord-1:0] data_flush_read_way;

    always_ff @(posedge clk_i)
    begin : data_flush_row_index_ff
        if (data_flush_read_i) data_flush_row_index_q <= data_ram_row;
    end

    hpdcache_mux #(
        .NINPUT      (HPDcacheCfg.u.ways/HPDcacheCfg.u.dataWaysPerRamWord),
        .DATA_WIDTH  (HPDcacheCfg.accessWidth*HPDcacheCfg.u.dataWaysPerRamWord),
        .ONE_HOT_SEL (1'b1)
    ) data_read_flush_mux_row_i(
        .data_i      (data_rentry),
        .sel_i       (data_flush_row_index_q),
        .data_o      (data_flush_row_data)
    );

    for (gen_i = 0; gen_i < HPDcacheCfg.u.dataWaysPerRamWord; gen_i++)
    begin : gen_data_flush_way_i
        for (gen_j = 0; gen_j < HPDcacheCfg.u.accessWords; gen_j++)
        begin : gen_data_flush_way_j
            assign data_flush_ways_data[gen_i][gen_j] = data_flush_row_data[gen_j][gen_i];
        end
    end

    always_comb
    begin : decode_flush_read_way_comb
        data_flush_read_way = '0;
        for (int i = 0; i < HPDcacheCfg.u.dataWaysPerRamWord; i++) begin
            for (int j = 0; j < HPDcacheCfg.u.ways; j += HPDcacheCfg.u.dataWaysPerRamWord) begin
                data_flush_read_way[i] |= data_flush_read_way_i[i + j];
            end
        end
    end

    hpdcache_mux #(
        .NINPUT      (HPDcacheCfg.u.dataWaysPerRamWord),
        .DATA_WIDTH  (HPDcacheCfg.accessWidth),
        .ONE_HOT_SEL (1'b1)
    ) data_read_flush_mux_way_i(
        .data_i      (data_flush_ways_data),
        .sel_i       (data_flush_read_way),
        .data_o      (data_flush_read_data_o)
    );
    //  }}}

    //  Assertions
    //  {{{
`ifndef HPDCACHE_ASSERT_OFF
    for (gen_i = 0; gen_i < HPDcacheCfg.u.ways; gen_i++) begin : gen_check_dirty_state
        check_dirty_state: assert property (@(posedge clk_i) disable iff (!rst_ni || !init_q)
                (dir_cs[gen_i] & ~dir_we[gen_i]) |=> (dir_dirty[gen_i] |-> dir_valid[gen_i])) else
                $error("hpdcache_memctrl: wrong directory state - dirty but not valid");
    end

    concurrent_dir_access_assert: assert property (@(posedge clk_i) disable iff (!rst_ni)
            $onehot0({dir_match_i,
                      dir_amo_match_i,
                      dir_refill_i,
                      dir_inval_check_i,
                      dir_inval_write_i,
                      dir_cmo_check_nline_i,
                      dir_cmo_check_entry_i,
                      dir_cmo_updt_i,
                      dir_updt_i})) else
            $error("hpdcache_memctrl: more than one process is accessing the cache directory");

    concurrent_data_access_assert: assert property (@(posedge clk_i) disable iff (!rst_ni)
            $onehot0({data_req_read_i,
                      data_req_write_i,
                      data_amo_write_i,
                      data_refill_i,
                      data_flush_read_i})) else
            $error("hpdcache_memctrl: more than one process is accessing the cache data");
`endif
    //  }}}
endmodule
