// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// Description: Functional module of a generic SRAM
//
// Parameters:
// - NumWords:    Number of words in the macro. Address width can be calculated with:
//                `AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1`
//                The module issues a warning if there is a request on an address which is
//                not in range.
// - DataWidth:   Width of the ports `wdata_i` and `rdata_o`.
// - ByteWidth:   Width of a byte, the byte enable signal `be_i` can be calculated with the
//                ceiling division `ceil(DataWidth, ByteWidth)`.
// - NumPorts:    Number of read and write ports. Each is a full port. Ports with a higher
//                index read and write after the ones with lower indices.
// - Latency:     Read latency, the read data is available this many cycles after a request.
// - SimInit:     Macro simulation initialization. Values are:
//                "zeros":  Each bit gets initialized with 1'b0.
//                "ones":   Each bit gets initialized with 1'b1.
//                "random": Each bit gets random initialized with 1'b0 or 1'b1.
//                "none":   Each bit gets initialized with 1'bx. (default)
// - PrintSimCfg: Prints at the beginning of the simulation a `Hello` message with
//                the instantiated parameters and signal widths.
// - ImplKey:     Key by which an instance can refer to a specific implementation (e.g. macro).
//                May be used to look up additional parameters for implementation (e.g. generator,
//                line width, muxing) in an external reference, such as a configuration file.
//
// Ports:
// - `clk_i`:   Clock
// - `rst_ni`:  Asynchronous reset, active low
// - `req_i`:   Request, active high
// - `we_i`:    Write request, active high
// - `addr_i`:  Request address
// - `wdata_i`: Write data, has to be valid on request
// - `be_i`:    Byte enable, active high
// - `rdata_o`: Read data, valid `Latency` cycles after a request with `we_i` low.
//
// Behaviour:
// - Address collision:  When Ports are making a write access onto the same address,
//                       the write operation will start at the port with the lowest address
//                       index, each port will overwrite the changes made by the previous ports
//                       according how the respective `be_i` signal is set.
// - Read data on write: This implementation will not produce a read data output on the signal
//                       `rdata_o` when `req_i` and `we_i` are asserted. The output data is stable
//                       on write requests.

module tc_sram #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte
  parameter int unsigned NumPorts     = 32'd2,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "none",   // Simulation initialization
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  parameter              ImplKey      = "none",   // Reference to specific implementation
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
  parameter type         addr_t    = logic [AddrWidth-1:0],
  parameter type         data_t    = logic [DataWidth-1:0],
  parameter type         be_t      = logic [BeWidth-1:0]
) (
  input  logic                 clk_i,      // Clock
  input  logic                 rst_ni,     // Asynchronous reset active low
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o     // read data
);

  // memory array
  data_t sram [NumWords-1:0];
  // hold the read address when no read access is made
  addr_t [NumPorts-1:0] r_addr_q;

  // SRAM simulation initialization
  data_t init_val[NumWords-1:0];
  initial begin : proc_sram_init
    for (int unsigned i = 0; i < NumWords; i++) begin
      case (SimInit)
        "zeros":  init_val[i] = {DataWidth{1'b0}};
        "ones":   init_val[i] = {DataWidth{1'b1}};
        "random": init_val[i] = {DataWidth{$urandom()}};
        default:  init_val[i] = {DataWidth{1'bx}};
      endcase
    end
  end

  // set the read output if requested
  // The read data at the highest array index is set combinational.
  // It gets then delayed for a number of cycles until it gets available at the output at
  // array index 0.

  // read data output assignment
  data_t [NumPorts-1:0][Latency-1:0] rdata_q,  rdata_d;
  if (Latency == 32'd0) begin : gen_no_read_lat
    for (genvar i = 0; i < NumPorts; i++) begin : gen_port
      assign rdata_o[i] = (req_i[i] && !we_i[i]) ? sram[addr_i[i]] : sram[r_addr_q[i]];
    end
  end else begin : gen_read_lat

    always_comb begin
      for (int unsigned i = 0; i < NumPorts; i++) begin
        rdata_o[i] = rdata_q[i][0];
        for (int unsigned j = 0; j < (Latency-1); j++) begin
          rdata_d[i][j] = rdata_q[i][j+1];
        end
        rdata_d[i][Latency-1] = (req_i[i] && !we_i[i]) ? sram[addr_i[i]] : sram[r_addr_q[i]];
      end
    end
  end

  // In case simulation initialization is disabled (SimInit == 'none'), don't assign to the sram
  // content at all. This improves simulation performance in tools like verilator
  if (SimInit == "none") begin
    // write memory array without initialization
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        for (int i = 0; i < NumPorts; i++) begin
          r_addr_q[i] <= {AddrWidth{1'b0}};
        end
      end else begin
        // read value latch happens before new data is written to the sram
        for (int unsigned i = 0; i < NumPorts; i++) begin
          if (Latency != 0) begin
            for (int unsigned j = 0; j < Latency; j++) begin
              rdata_q[i][j] <= rdata_d[i][j];
            end
          end
        end
        // there is a request for the SRAM, latch the required register
        for (int unsigned i = 0; i < NumPorts; i++) begin
          if (req_i[i]) begin
            if (we_i[i]) begin
              // update value when write is set at clock
              for (int unsigned j = 0; j < BeWidth; j++) begin
                if (be_i[i][j]) begin
                  sram[addr_i[i]][j*ByteWidth+:ByteWidth] <= wdata_i[i][j*ByteWidth+:ByteWidth];
                end
              end
            end else begin
              // otherwise update read address for subsequent non request cycles
              r_addr_q[i] <= addr_i[i];
            end
          end // if req_i
        end // for ports
      end // if !rst_ni
    end
  end else begin
    // write memory array
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        // Fix to avoid runtime space reaching maximum capacity in simulation
        foreach (init_val[i]) begin
          sram[i] <= init_val[i];
        end
        for (int i = 0; i < NumPorts; i++) begin
          r_addr_q[i] <= {AddrWidth{1'b0}};
          // initialize the read output register for each port
          if (Latency != 32'd0) begin
            for (int unsigned j = 0; j < Latency; j++) begin
              rdata_q[i][j] <= init_val[{AddrWidth{1'b0}}];
            end
          end
        end
      end else begin
        // read value latch happens before new data is written to the sram
        for (int unsigned i = 0; i < NumPorts; i++) begin
          if (Latency != 0) begin
            for (int unsigned j = 0; j < Latency; j++) begin
              rdata_q[i][j] <= rdata_d[i][j];
            end
          end
        end
        // there is a request for the SRAM, latch the required register
        for (int unsigned i = 0; i < NumPorts; i++) begin
          if (req_i[i]) begin
            if (we_i[i]) begin
              // update value when write is set at clock
              for (int unsigned j = 0; j < BeWidth; j++) begin
                if (be_i[i][j]) begin
                  sram[addr_i[i]][j*ByteWidth+:ByteWidth] <= wdata_i[i][j*ByteWidth+:ByteWidth];
                end
              end
            end else begin
              // otherwise update read address for subsequent non request cycles
              r_addr_q[i] <= addr_i[i];
            end
          end // if req_i
        end // for ports
      end // if !rst_ni
    end
  end

// Validate parameters.
// pragma translate_off
`ifndef VERILATOR
`ifndef TARGET_SYNTHESIS
  initial begin: p_assertions
    assert ($bits(addr_i)  == NumPorts * AddrWidth) else $fatal(1, "AddrWidth problem on `addr_i`");
    assert ($bits(wdata_i) == NumPorts * DataWidth) else $fatal(1, "DataWidth problem on `wdata_i`");
    assert ($bits(be_i)    == NumPorts * BeWidth)   else $fatal(1, "BeWidth   problem on `be_i`"   );
    assert ($bits(rdata_o) == NumPorts * DataWidth) else $fatal(1, "DataWidth problem on `rdata_o`");
    assert (NumWords  >= 32'd1) else $fatal(1, "NumWords has to be > 0");
    assert (DataWidth >= 32'd1) else $fatal(1, "DataWidth has to be > 0");
    assert (ByteWidth >= 32'd1) else $fatal(1, "ByteWidth has to be > 0");
    assert (NumPorts  >= 32'd1) else $fatal(1, "The number of ports must be at least 1!");
  end
  initial begin: p_sim_hello
    if (PrintSimCfg) begin
      $display("#################################################################################");
      $display("tc_sram functional instantiated with the configuration:"                          );
      $display("Instance: %m"                                                                     );
      $display("Number of ports   (dec): %0d", NumPorts                                           );
      $display("Number of words   (dec): %0d", NumWords                                           );
      $display("Address width     (dec): %0d", AddrWidth                                          );
      $display("Data width        (dec): %0d", DataWidth                                          );
      $display("Byte width        (dec): %0d", ByteWidth                                          );
      $display("Byte enable width (dec): %0d", BeWidth                                            );
      $display("Latency Cycles    (dec): %0d", Latency                                            );
      $display("Simulation init   (str): %0s", SimInit                                            );
      $display("#################################################################################");
    end
  end
  for (genvar i = 0; i < NumPorts; i++) begin : gen_assertions
    assert property ( @(posedge clk_i) disable iff (!rst_ni)
        (req_i[i] |-> (addr_i[i] < NumWords))) else
      $warning("Request address %0h not mapped, port %0d, expect random write or read behavior!",
          addr_i[i], i);
  end

`endif
`endif
// pragma translate_on
endmodule
