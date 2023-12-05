// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "common_cells/registers.svh"
/// AXI4+ATOP slave module which translates AXI bursts into a memory stream.
/// If both read and write channels of the AXI4+ATOP are active, both will have an
/// utilization of 50%.
module axi_to_detailed_mem #(
  /// AXI4+ATOP request type. See `include/axi/typedef.svh`.
  parameter type         axi_req_t  = logic,
  /// AXI4+ATOP response type. See `include/axi/typedef.svh`.
  parameter type         axi_resp_t = logic,
  /// Address width, has to be less or equal than the width off the AXI address field.
  /// Determines the width of `mem_addr_o`. Has to be wide enough to emit the memory region
  /// which should be accessible.
  parameter int unsigned AddrWidth  = 0,
  /// AXI4+ATOP data width.
  parameter int unsigned DataWidth  = 0,
  /// AXI4+ATOP ID width.
  parameter int unsigned IdWidth    = 0,
  /// AXI4+ATOP user width.
  parameter int unsigned UserWidth  = 0,
  /// Number of banks at output, must evenly divide `DataWidth`.
  parameter int unsigned NumBanks   = 0,
  /// Depth of memory response buffer. This should be equal to the memory response latency.
  parameter int unsigned BufDepth   = 1,
  /// Hide write requests if the strb == '0
  parameter bit          HideStrb   = 1'b0,
  /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
  parameter int unsigned OutFifoDepth = 1,
  /// Dependent parameter, do not override. Memory address type.
  localparam type addr_t     = logic [AddrWidth-1:0],
  /// Dependent parameter, do not override. Memory data type.
  localparam type mem_data_t = logic [DataWidth/NumBanks-1:0],
  /// Dependent parameter, do not override. Memory write strobe type.
  localparam type mem_strb_t = logic [DataWidth/NumBanks/8-1:0],
  /// Dependent parameter, do not override. Memory id type.
  localparam type mem_id_t   = logic [IdWidth-1:0],
  /// Dependent parameter, do not override. Memory user type.
  localparam type mem_user_t = logic [UserWidth-1:0]
) (
  /// Clock input.
  input  logic                             clk_i,
  /// Asynchronous reset, active low.
  input  logic                             rst_ni,
  /// The unit is busy handling an AXI4+ATOP request.
  output logic                             busy_o,
  /// AXI4+ATOP slave port, request input.
  input  axi_req_t                         axi_req_i,
  /// AXI4+ATOP slave port, response output.
  output axi_resp_t                        axi_resp_o,
  /// Memory stream master, request is valid for this bank.
  output logic             [NumBanks-1:0]  mem_req_o,
  /// Memory stream master, request can be granted by this bank.
  input  logic             [NumBanks-1:0]  mem_gnt_i,
  /// Memory stream master, byte address of the request.
  output addr_t            [NumBanks-1:0]  mem_addr_o,
  /// Memory stream master, write data for this bank. Valid when `mem_req_o`.
  output mem_data_t        [NumBanks-1:0]  mem_wdata_o,
  /// Memory stream master, byte-wise strobe (byte enable).
  output mem_strb_t        [NumBanks-1:0]  mem_strb_o,
  /// Memory stream master, `axi_pkg::atop_t` signal associated with this request.
  output axi_pkg::atop_t   [NumBanks-1:0]  mem_atop_o,
  /// Memory stream master, lock signal.
  output logic             [NumBanks-1:0]  mem_lock_o,
  /// Memory stream master, write enable. Then asserted store of `mem_w_data` is requested.
  output logic             [NumBanks-1:0]  mem_we_o,
  /// Memory stream master, ID. Response ID is managed internally, ensure in-order responses.
  output mem_id_t          [NumBanks-1:0]  mem_id_o,
  /// Memory stream master, user signal. Ax channel user bits used.
  output mem_user_t        [NumBanks-1:0]  mem_user_o,
  /// Memory stream master, cache signal.
  output axi_pkg::cache_t  [NumBanks-1:0]  mem_cache_o,
  /// Memory stream master, protection signal.
  output axi_pkg::prot_t   [NumBanks-1:0]  mem_prot_o,
  /// Memory stream master, QOS signal.
  output axi_pkg::qos_t    [NumBanks-1:0]  mem_qos_o,
  /// Memory stream master, region signal.
  output axi_pkg::region_t [NumBanks-1:0]  mem_region_o,
  /// Memory stream master, response is valid. This module expects always a response valid for a
  /// request regardless if the request was a write or a read.
  input  logic             [NumBanks-1:0]  mem_rvalid_i,
  /// Memory stream master, read response data.
  input  mem_data_t        [NumBanks-1:0]  mem_rdata_i,
  /// Memory stream master, error response.
  input  logic             [NumBanks-1:0]  mem_err_i,
  /// Memory stream master, read response exclusive access OK.
  input  logic             [NumBanks-1:0]  mem_exokay_i
);

  typedef logic [DataWidth-1:0]   axi_data_t;
  typedef logic [DataWidth/8-1:0] axi_strb_t;
  typedef logic [IdWidth-1:0]     axi_id_t;

  typedef struct packed {
    addr_t            addr;
    axi_pkg::atop_t   atop;
    logic             lock;
    axi_strb_t        strb;
    axi_data_t        wdata;
    logic             we;
    mem_id_t          id;
    mem_user_t        user;
    axi_pkg::cache_t  cache;
    axi_pkg::prot_t   prot;
    axi_pkg::qos_t    qos;
    axi_pkg::region_t region;
  } mem_req_t;

  typedef struct packed {
    addr_t            addr;
    axi_pkg::atop_t   atop;
    logic             lock;
    axi_strb_t        strb;
    axi_id_t          id;
    logic             last;
    axi_pkg::qos_t    qos;
    axi_pkg::size_t   size;
    logic             write;
    mem_user_t        user;
    axi_pkg::cache_t  cache;
    axi_pkg::prot_t   prot;
    axi_pkg::region_t region;
  } meta_t;

  typedef struct packed {
    axi_data_t           data;
    logic [NumBanks-1:0] err;
    logic [NumBanks-1:0] exokay;
  } mem_rsp_t;

  mem_rsp_t       mem_rdata,
                  m2s_resp;
  axi_pkg::len_t  r_cnt_d,        r_cnt_q,
                  w_cnt_d,        w_cnt_q;
  logic           arb_valid,      arb_ready,
                  rd_valid,       rd_ready,
                  wr_valid,       wr_ready,
                  sel_b,          sel_buf_b,
                  sel_r,          sel_buf_r,
                  sel_valid,      sel_ready,
                  sel_buf_valid,  sel_buf_ready,
                  sel_lock_d,     sel_lock_q,
                  meta_valid,     meta_ready,
                  meta_buf_valid, meta_buf_ready,
                  meta_sel_d,     meta_sel_q,
                  m2s_req_valid,  m2s_req_ready,
                  m2s_resp_valid, m2s_resp_ready,
                  mem_req_valid,  mem_req_ready,
                  mem_rvalid;
  mem_req_t       m2s_req,
                  mem_req;
  meta_t          rd_meta,
                  rd_meta_d,      rd_meta_q,
                  wr_meta,
                  wr_meta_d,      wr_meta_q,
                  meta,           meta_buf;

  assign busy_o = axi_req_i.aw_valid | axi_req_i.ar_valid | axi_req_i.w_valid |
                    axi_resp_o.b_valid | axi_resp_o.r_valid |
                    (r_cnt_q > 0) | (w_cnt_q > 0);

  // Handle reads.
  always_comb begin
    // Default assignments
    axi_resp_o.ar_ready = 1'b0;
    rd_meta_d           = rd_meta_q;
    rd_meta             = meta_t'{default: '0};
    rd_valid            = 1'b0;
    r_cnt_d             = r_cnt_q;
    // Handle R burst in progress.
    if (r_cnt_q > '0) begin
      rd_meta_d.last = (r_cnt_q == 8'd1);
      rd_meta        = rd_meta_d;
      rd_meta.addr   = rd_meta_q.addr + axi_pkg::num_bytes(rd_meta_q.size);
      rd_valid       = 1'b1;
      if (rd_ready) begin
        r_cnt_d--;
        rd_meta_d.addr = rd_meta.addr;
      end
    // Handle new AR if there is one.
    end else if (axi_req_i.ar_valid) begin
      rd_meta_d = '{
        addr:   addr_t'(axi_pkg::aligned_addr(axi_req_i.ar.addr, axi_req_i.ar.size)),
        atop:   '0,
        lock:   axi_req_i.ar.lock,
        strb:   '0,
        id:     axi_req_i.ar.id,
        last:   (axi_req_i.ar.len == '0),
        qos:    axi_req_i.ar.qos,
        size:   axi_req_i.ar.size,
        write:  1'b0,
        user:   axi_req_i.ar.user,
        cache:  axi_req_i.ar.cache,
        prot:   axi_req_i.ar.prot,
        region: axi_req_i.ar.region
      };
      rd_meta      = rd_meta_d;
      rd_meta.addr = addr_t'(axi_req_i.ar.addr);
      rd_valid     = 1'b1;
      if (rd_ready) begin
        r_cnt_d             = axi_req_i.ar.len;
        axi_resp_o.ar_ready = 1'b1;
      end
    end
  end

  // Handle writes.
  always_comb begin
    // Default assignments
    axi_resp_o.aw_ready = 1'b0;
    axi_resp_o.w_ready  = 1'b0;
    wr_meta_d           = wr_meta_q;
    wr_meta             = meta_t'{default: '0};
    wr_valid            = 1'b0;
    w_cnt_d             = w_cnt_q;
    // Handle W bursts in progress.
    if (w_cnt_q > '0) begin
      wr_meta_d.last = (w_cnt_q == 8'd1);
      wr_meta        = wr_meta_d;
      wr_meta.addr   = wr_meta_q.addr + axi_pkg::num_bytes(wr_meta_q.size);
      if (axi_req_i.w_valid) begin
        wr_valid = 1'b1;
        wr_meta.strb = axi_req_i.w.strb;
        if (wr_ready) begin
          axi_resp_o.w_ready = 1'b1;
          w_cnt_d--;
          wr_meta_d.addr = wr_meta.addr;
        end
      end
    // Handle new AW if there is one.
    end else if (axi_req_i.aw_valid && axi_req_i.w_valid) begin
      wr_meta_d = '{
        addr:   addr_t'(axi_pkg::aligned_addr(axi_req_i.aw.addr, axi_req_i.aw.size)),
        atop:   axi_req_i.aw.atop,
        lock:   axi_req_i.aw.lock,
        strb:   axi_req_i.w.strb,
        id:     axi_req_i.aw.id,
        last:   (axi_req_i.aw.len == '0),
        qos:    axi_req_i.aw.qos,
        size:   axi_req_i.aw.size,
        write:  1'b1,
        user:   axi_req_i.aw.user,
        cache:  axi_req_i.aw.cache,
        prot:   axi_req_i.aw.prot,
        region: axi_req_i.aw.region
      };
      wr_meta = wr_meta_d;
      wr_meta.addr = addr_t'(axi_req_i.aw.addr);
      wr_valid = 1'b1;
      if (wr_ready) begin
        w_cnt_d = axi_req_i.aw.len;
        axi_resp_o.aw_ready = 1'b1;
        axi_resp_o.w_ready = 1'b1;
      end
    end
  end

  // Arbitrate between reads and writes.
  stream_mux #(
    .DATA_T ( meta_t ),
    .N_INP  ( 32'd2  )
  ) i_ax_mux (
    .inp_data_i   ({wr_meta,  rd_meta }),
    .inp_valid_i  ({wr_valid, rd_valid}),
    .inp_ready_o  ({wr_ready, rd_ready}),
    .inp_sel_i    ( meta_sel_d         ),
    .oup_data_o   ( meta               ),
    .oup_valid_o  ( arb_valid          ),
    .oup_ready_i  ( arb_ready          )
  );
  always_comb begin
    meta_sel_d = meta_sel_q;
    sel_lock_d = sel_lock_q;
    if (sel_lock_q) begin
      meta_sel_d = meta_sel_q;
      if (arb_valid && arb_ready) begin
        sel_lock_d = 1'b0;
      end
    end else begin
      if (wr_valid ^ rd_valid) begin
        // If either write or read is valid but not both, select the valid one.
        meta_sel_d = wr_valid;
      end else if (wr_valid && rd_valid) begin
        // If both write and read are valid, decide according to QoS then burst properties.
        // Prioritize higher QoS.
        if (wr_meta.qos > rd_meta.qos) begin
          meta_sel_d = 1'b1;
        end else if (rd_meta.qos > wr_meta.qos) begin
          meta_sel_d = 1'b0;
        // Decide requests with identical QoS.
        end else if (wr_meta.qos == rd_meta.qos) begin
          // 1. Prioritize individual writes over read bursts.
          // Rationale: Read bursts can be interleaved on AXI but write bursts cannot.
          if (wr_meta.last && !rd_meta.last) begin
            meta_sel_d = 1'b1;
          // 2. Prioritize ongoing burst.
          // Rationale: Stalled bursts create back-pressure or require costly buffers.
          end else if (w_cnt_q > '0) begin
            meta_sel_d = 1'b1;
          end else if (r_cnt_q > '0) begin
            meta_sel_d = 1'b0;
          // 3. Otherwise arbitrate round robin to prevent starvation.
          end else begin
            meta_sel_d = ~meta_sel_q;
          end
        end
      end
      // Lock arbitration if valid but not yet ready.
      if (arb_valid && !arb_ready) begin
        sel_lock_d = 1'b1;
      end
    end
  end

  // Fork arbitrated stream to meta data, memory requests, and R/B channel selection.
  stream_fork #(
    .N_OUP ( 32'd3 )
  ) i_fork (
    .clk_i,
    .rst_ni,
    .valid_i ( arb_valid                            ),
    .ready_o ( arb_ready                            ),
    .valid_o ({sel_valid, meta_valid, m2s_req_valid}),
    .ready_i ({sel_ready, meta_ready, m2s_req_ready})
  );

  assign sel_b = meta.write & meta.last;
  assign sel_r = ~meta.write | meta.atop[5];

  stream_fifo #(
    .FALL_THROUGH ( 1'b1             ),
    .DEPTH        ( 32'd1 + BufDepth ),
    .T            ( logic[1:0]       )
  ) i_sel_buf (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0                    ),
    .testmode_i ( 1'b0                    ),
    .data_i     ({sel_b,        sel_r    }),
    .valid_i    ( sel_valid               ),
    .ready_o    ( sel_ready               ),
    .data_o     ({sel_buf_b,    sel_buf_r}),
    .valid_o    ( sel_buf_valid           ),
    .ready_i    ( sel_buf_ready           ),
    .usage_o    ( /* unused */            )
  );

  stream_fifo #(
    .FALL_THROUGH ( 1'b1             ),
    .DEPTH        ( 32'd1 + BufDepth ),
    .T            ( meta_t           )
  ) i_meta_buf (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0           ),
    .testmode_i ( 1'b0           ),
    .data_i     ( meta           ),
    .valid_i    ( meta_valid     ),
    .ready_o    ( meta_ready     ),
    .data_o     ( meta_buf       ),
    .valid_o    ( meta_buf_valid ),
    .ready_i    ( meta_buf_ready ),
    .usage_o    ( /* unused */   )
  );

  // Assemble the actual memory request from meta information and write data.
  assign m2s_req = mem_req_t'{
    addr:   meta.addr,
    atop:   meta.atop,
    lock:   meta.lock,
    strb:   axi_req_i.w.strb,
    wdata:  axi_req_i.w.data,
    we:     meta.write,
    id:     meta.id,
    user:   meta.user,
    cache:  meta.cache,
    prot:   meta.prot,
    qos:    meta.qos,
    region: meta.region
  };

  // Interface memory as stream.
  stream_to_mem #(
    .mem_req_t  ( mem_req_t  ),
    .mem_resp_t ( mem_rsp_t  ),
    .BufDepth   ( BufDepth   )
  ) i_stream_to_mem (
    .clk_i,
    .rst_ni,
    .req_i            ( m2s_req        ),
    .req_valid_i      ( m2s_req_valid  ),
    .req_ready_o      ( m2s_req_ready  ),
    .resp_o           ( m2s_resp       ),
    .resp_valid_o     ( m2s_resp_valid ),
    .resp_ready_i     ( m2s_resp_ready ),
    .mem_req_o        ( mem_req        ),
    .mem_req_valid_o  ( mem_req_valid  ),
    .mem_req_ready_i  ( mem_req_ready  ),
    .mem_resp_i       ( mem_rdata      ),
    .mem_resp_valid_i ( mem_rvalid     )
  );

  typedef struct packed {
    axi_pkg::atop_t   atop;
    logic             lock;
    mem_id_t          id;
    mem_user_t        user;
    axi_pkg::cache_t  cache;
    axi_pkg::prot_t   prot;
    axi_pkg::qos_t    qos;
    axi_pkg::region_t region;
  } tmp_atop_t;

  tmp_atop_t mem_req_atop;
  tmp_atop_t [NumBanks-1:0] banked_req_atop;

  assign mem_req_atop = '{
    atop:   mem_req.atop,
    lock:   mem_req.lock,
    id:     mem_req.id,
    user:   mem_req.user,
    cache:  mem_req.cache,
    prot:   mem_req.prot,
    qos:    mem_req.qos,
    region: mem_req.region
  };

  for (genvar i = 0; i < NumBanks; i++) begin
    assign mem_atop_o  [i] = banked_req_atop[i].atop;
    assign mem_lock_o  [i] = banked_req_atop[i].lock;
    assign mem_id_o    [i] = banked_req_atop[i].id;
    assign mem_user_o  [i] = banked_req_atop[i].user;
    assign mem_cache_o [i] = banked_req_atop[i].cache;
    assign mem_prot_o  [i] = banked_req_atop[i].prot;
    assign mem_qos_o   [i] = banked_req_atop[i].qos;
    assign mem_region_o[i] = banked_req_atop[i].region;
  end

  logic [NumBanks-1:0][1:0] tmp_ersp;
  logic [NumBanks-1:0][1:0] bank_ersp;
  for (genvar i = 0; i < NumBanks; i++) begin
    assign mem_rdata.err[i]    = tmp_ersp[i][0];
    assign mem_rdata.exokay[i] = tmp_ersp[i][1];
    assign bank_ersp[i][0] = mem_err_i[i];
    assign bank_ersp[i][1] = mem_exokay_i[i];
  end

  // Split single memory request to desired number of banks.
  mem_to_banks_detailed #(
    .AddrWidth  ( AddrWidth         ),
    .DataWidth  ( DataWidth         ),
    .RUserWidth ( 2                 ),
    .NumBanks   ( NumBanks          ),
    .HideStrb   ( HideStrb          ),
    .MaxTrans   ( BufDepth          ),
    .FifoDepth  ( OutFifoDepth      ),
    .WUserWidth ( $bits(tmp_atop_t) )
  ) i_mem_to_banks (
    .clk_i,
    .rst_ni,
    .req_i         ( mem_req_valid ),
    .gnt_o         ( mem_req_ready ),
    .addr_i        ( mem_req.addr  ),
    .wdata_i       ( mem_req.wdata ),
    .strb_i        ( mem_req.strb  ),
    .wuser_i       ( mem_req_atop  ),
    .we_i          ( mem_req.we    ),
    .rvalid_o      ( mem_rvalid    ),
    .rdata_o       ( mem_rdata.data ),
    .ruser_o       ( tmp_ersp      ),
    .bank_req_o    ( mem_req_o     ),
    .bank_gnt_i    ( mem_gnt_i     ),
    .bank_addr_o   ( mem_addr_o    ),
    .bank_wdata_o  ( mem_wdata_o   ),
    .bank_strb_o   ( mem_strb_o    ),
    .bank_wuser_o  ( banked_req_atop ),
    .bank_we_o     ( mem_we_o      ),
    .bank_rvalid_i ( mem_rvalid_i  ),
    .bank_rdata_i  ( mem_rdata_i   ),
    .bank_ruser_i  ( bank_ersp     )
  );

  // Join memory read data and meta data stream.
  logic mem_join_valid, mem_join_ready;
  stream_join #(
    .N_INP ( 32'd2 )
  ) i_join (
    .inp_valid_i  ({m2s_resp_valid, meta_buf_valid}),
    .inp_ready_o  ({m2s_resp_ready, meta_buf_ready}),
    .oup_valid_o  ( mem_join_valid                 ),
    .oup_ready_i  ( mem_join_ready                 )
  );

  // Dynamically fork the joined stream to B and R channels.
  stream_fork_dynamic #(
    .N_OUP ( 32'd2 )
  ) i_fork_dynamic (
    .clk_i,
    .rst_ni,
    .valid_i      ( mem_join_valid                         ),
    .ready_o      ( mem_join_ready                         ),
    .sel_i        ({sel_buf_b,          sel_buf_r         }),
    .sel_valid_i  ( sel_buf_valid                          ),
    .sel_ready_o  ( sel_buf_ready                          ),
    .valid_o      ({axi_resp_o.b_valid, axi_resp_o.r_valid}),
    .ready_i      ({axi_req_i.b_ready,  axi_req_i.r_ready })
  );

  localparam NumBytesPerBank = DataWidth/NumBanks/8;

  logic [NumBanks-1:0] meta_buf_bank_strb, meta_buf_size_enable;
  logic resp_b_err, resp_b_exokay, resp_r_err, resp_r_exokay;

  // Collect `err` and `exokay` from all banks
  // To ensure correct propagation, `err` is grouped with `OR` and `exokay` is grouped with `AND`.
  for (genvar i = 0; i < NumBanks; i++) begin
    // Set active write banks based on strobe
    assign meta_buf_bank_strb[i] = |meta_buf.strb[i*NumBytesPerBank +: NumBytesPerBank];
    // Set active read banks based on size and address offset: (bank.end > addr) && (bank.start < addr+size)
    assign meta_buf_size_enable[i] = ((i*NumBytesPerBank + NumBytesPerBank) > (meta_buf.addr % DataWidth/8)) &&
                                     ((i*NumBytesPerBank) < ((meta_buf.addr % DataWidth/8) + 1<<meta_buf.size));
  end
  assign resp_b_err    = |(m2s_resp.err    &  meta_buf_bank_strb);   // Ensure only active banks are used (strobe)
  assign resp_b_exokay = &(m2s_resp.exokay | ~meta_buf_bank_strb);   // Ensure only active banks are used (strobe)
  assign resp_r_err    = |(m2s_resp.err    &  meta_buf_size_enable); // Ensure only active banks are used (size & addr offset)
  assign resp_r_exokay = &(m2s_resp.exokay | ~meta_buf_size_enable); // Ensure only active banks are used (size & addr offset)

  logic collect_b_err_d, collect_b_err_q;
  logic collect_b_exokay_d, collect_b_exokay_q;
  logic next_collect_b_err, next_collect_b_exokay;

  // Accumulate write errors for single B response
  // To ensure correct propagation, `err` is grouped with `OR` and `exokay` is grouped with `AND`.
  assign next_collect_b_err = collect_b_err_q | resp_b_err;
  assign next_collect_b_exokay = collect_b_exokay_q & resp_b_exokay;

  always_comb begin
    // By default we keep the previous value
    collect_b_err_d = collect_b_err_q;
    collect_b_exokay_d = collect_b_exokay_q;
    // If the buffer is properly popped
    if (sel_buf_valid && sel_buf_ready) begin
      if (meta_buf.write && meta_buf.last) begin
        collect_b_err_d = 1'b0;
        collect_b_exokay_d = 1'b1;
      end else if (meta_buf.write) begin
        collect_b_err_d = next_collect_b_err;
        collect_b_exokay_d = next_collect_b_exokay;
      end
    end
  end

  // Compose B responses.
  assign axi_resp_o.b = '{
    id:   meta_buf.id,
    resp: next_collect_b_err ? axi_pkg::RESP_SLVERR : next_collect_b_exokay ? axi_pkg::RESP_EXOKAY : axi_pkg::RESP_OKAY,
    user: '0
  };

  // Compose R responses.
  assign axi_resp_o.r = '{
    data: m2s_resp.data,
    id:   meta_buf.id,
    last: meta_buf.last,
    resp: resp_r_err ? axi_pkg::RESP_SLVERR : resp_r_exokay ? axi_pkg::RESP_EXOKAY : axi_pkg::RESP_OKAY,
    user: '0
  };

  // Registers
  `FFARN(meta_sel_q, meta_sel_d, 1'b0, clk_i, rst_ni)
  `FFARN(sel_lock_q, sel_lock_d, 1'b0, clk_i, rst_ni)
  `FFARN(rd_meta_q, rd_meta_d, meta_t'{default: '0}, clk_i, rst_ni)
  `FFARN(wr_meta_q, wr_meta_d, meta_t'{default: '0}, clk_i, rst_ni)
  `FFARN(r_cnt_q, r_cnt_d, '0, clk_i, rst_ni)
  `FFARN(w_cnt_q, w_cnt_d, '0, clk_i, rst_ni)
  `FFARN(collect_b_err_q, collect_b_err_d, '0, clk_i, rst_ni)
  `FFARN(collect_b_exokay_q, collect_b_exokay_d, 1'b1, clk_i, rst_ni)

  // Assertions
  // pragma translate_off
  `ifndef VERILATOR
  default disable iff (!rst_ni);
  assume property (@(posedge clk_i)
      axi_req_i.ar_valid && !axi_resp_o.ar_ready |=> $stable(axi_req_i.ar))
    else $error("AR must remain stable until handshake has happened!");
  assert property (@(posedge clk_i)
      axi_resp_o.r_valid && !axi_req_i.r_ready |=> $stable(axi_resp_o.r))
    else $error("R must remain stable until handshake has happened!");
  assume property (@(posedge clk_i)
      axi_req_i.aw_valid && !axi_resp_o.aw_ready |=> $stable(axi_req_i.aw))
    else $error("AW must remain stable until handshake has happened!");
  assume property (@(posedge clk_i)
      axi_req_i.w_valid && !axi_resp_o.w_ready |=> $stable(axi_req_i.w))
    else $error("W must remain stable until handshake has happened!");
  assert property (@(posedge clk_i)
      axi_resp_o.b_valid && !axi_req_i.b_ready |=> $stable(axi_resp_o.b))
    else $error("B must remain stable until handshake has happened!");
  assert property (@(posedge clk_i) axi_req_i.ar_valid && axi_req_i.ar.len > 0 |->
      axi_req_i.ar.burst == axi_pkg::BURST_INCR)
    else $error("Non-incrementing bursts are not supported!");
  assert property (@(posedge clk_i) axi_req_i.aw_valid && axi_req_i.aw.len > 0 |->
      axi_req_i.aw.burst == axi_pkg::BURST_INCR)
    else $error("Non-incrementing bursts are not supported!");
  assert property (@(posedge clk_i) meta_valid && meta.atop != '0 |-> meta.write)
    else $warning("Unexpected atomic operation on read.");
  `endif
  // pragma translate_on
endmodule


`include "axi/assign.svh"
`include "axi/typedef.svh"
/// Interface wrapper for module `axi_to_mem`.
module axi_to_detailed_mem_intf #(
  /// See `axi_to_mem`, parameter `AddrWidth`.
  parameter int unsigned ADDR_WIDTH     = 32'd0,
  /// See `axi_to_mem`, parameter `DataWidth`.
  parameter int unsigned DATA_WIDTH     = 32'd0,
  /// AXI4+ATOP ID width.
  parameter int unsigned ID_WIDTH       = 32'd0,
  /// AXI4+ATOP user width.
  parameter int unsigned USER_WIDTH     = 32'd0,
  /// See `axi_to_mem`, parameter `NumBanks`.
  parameter int unsigned NUM_BANKS      = 32'd0,
  /// See `axi_to_mem`, parameter `BufDepth`.
  parameter int unsigned BUF_DEPTH      = 32'd1,
  /// Hide write requests if the strb == '0
  parameter bit          HIDE_STRB      = 1'b0,
  /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
  parameter int unsigned OUT_FIFO_DEPTH = 32'd1,
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `addr_t`.
  localparam type addr_t     = logic [ADDR_WIDTH-1:0],
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `mem_data_t`.
  localparam type mem_data_t = logic [DATA_WIDTH/NUM_BANKS-1:0],
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `mem_strb_t`.
  localparam type mem_strb_t = logic [DATA_WIDTH/NUM_BANKS/8-1:0]
) (
  /// Clock input.
  input  logic                              clk_i,
  /// Asynchronous reset, active low.
  input  logic                              rst_ni,
  /// See `axi_to_mem`, port `busy_o`.
  output logic                              busy_o,
  /// AXI4+ATOP slave interface port.
  AXI_BUS.Slave                             slv,
  /// See `axi_to_mem`, port `mem_req_o`.
  output logic             [NUM_BANKS-1:0]  mem_req_o,
  /// See `axi_to_mem`, port `mem_gnt_i`.
  input  logic             [NUM_BANKS-1:0]  mem_gnt_i,
  /// See `axi_to_mem`, port `mem_addr_o`.
  output addr_t            [NUM_BANKS-1:0]  mem_addr_o,
  /// See `axi_to_mem`, port `mem_wdata_o`.
  output mem_data_t        [NUM_BANKS-1:0]  mem_wdata_o,
  /// See `axi_to_mem`, port `mem_strb_o`.
  output mem_strb_t        [NUM_BANKS-1:0]  mem_strb_o,
  /// See `axi_to_mem`, port `mem_atop_o`.
  output axi_pkg::atop_t   [NUM_BANKS-1:0]  mem_atop_o,
  /// See `axi_to_mem`, port `mem_lock_o`.
  output logic             [NUM_BANKS-1:0]  mem_lock_o,
  /// See `axi_to_mem`, port `mem_we_o`.
  output logic             [NUM_BANKS-1:0]  mem_we_o,
  /// See `axi_to_mem`, port `mem_id_o`.
  output logic             [NUM_BANKS-1:0]  mem_id_o,
  /// See `axi_to_mem`, port `mem_user_o`.
  output logic             [NUM_BANKS-1:0]  mem_user_o,
  /// See `axi_to_mem`, port `mem_cache_o`.
  output axi_pkg::cache_t  [NUM_BANKS-1:0]  mem_cache_o,
  /// See `axi_to_mem`, port `mem_prot_o`.
  output axi_pkg::prot_t   [NUM_BANKS-1:0]  mem_prot_o,
  /// See `axi_to_mem`, port `mem_qos_o`.
  output axi_pkg::qos_t    [NUM_BANKS-1:0]  mem_qos_o,
  /// See `axi_to_mem`, port `mem_region_o`.
  output axi_pkg::region_t [NUM_BANKS-1:0]  mem_region_o,
  /// See `axi_to_mem`, port `mem_rvalid_i`.
  input  logic             [NUM_BANKS-1:0]  mem_rvalid_i,
  /// See `axi_to_mem`, port `mem_rdata_i`.
  input  mem_data_t        [NUM_BANKS-1:0]  mem_rdata_i,
  /// See `axi_to_mem`, port `mem_err_i`.
  input  logic             [NUM_BANKS-1:0]  mem_err_i,
  /// See `axi_to_mem`, port `mem_exokay_i`.
  input  logic             [NUM_BANKS-1:0]  mem_exokay_i
);
  typedef logic [ID_WIDTH-1:0]     id_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
  req_t   req;
  resp_t  resp;
  `AXI_ASSIGN_TO_REQ(req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, resp)
  axi_to_detailed_mem #(
    .axi_req_t    ( req_t          ),
    .axi_resp_t   ( resp_t         ),
    .AddrWidth    ( ADDR_WIDTH     ),
    .DataWidth    ( DATA_WIDTH     ),
    .IdWidth      ( ID_WIDTH       ),
    .UserWidth    ( USER_WIDTH     ),
    .NumBanks     ( NUM_BANKS      ),
    .BufDepth     ( BUF_DEPTH      ),
    .HideStrb     ( HIDE_STRB      ),
    .OutFifoDepth ( OUT_FIFO_DEPTH )
  ) i_axi_to_detailed_mem (
    .clk_i,
    .rst_ni,
    .busy_o,
    .axi_req_i  ( req  ),
    .axi_resp_o ( resp ),
    .mem_req_o,
    .mem_gnt_i,
    .mem_addr_o,
    .mem_wdata_o,
    .mem_strb_o,
    .mem_atop_o,
    .mem_lock_o,
    .mem_we_o,
    .mem_id_o,
    .mem_user_o,
    .mem_cache_o,
    .mem_prot_o,
    .mem_qos_o,
    .mem_region_o,
    .mem_rvalid_i,
    .mem_rdata_i,
    .mem_err_i,
    .mem_exokay_i
  );
endmodule
