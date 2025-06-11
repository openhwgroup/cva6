// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// test bench for addr_decode module

module addr_decode_tb;
  localparam int unsigned NoIndices =  2;
  localparam int unsigned NoRules   =  3;
  localparam int unsigned AddrWidth = 12;


  typedef logic [AddrWidth-1:0]         addr_t;
  typedef logic [$clog2(NoIndices)-1:0] idx_t;
  // struct to be used in the tb
  typedef struct packed {
    int unsigned idx;
    addr_t       start_addr;
    addr_t       end_addr;
  } tb_rule_t;

  // normal map
  localparam tb_rule_t [NoRules-1:0] map_0 = '{
    '{idx: 32'd0, start_addr: 12'h000, end_addr: 12'h010},
    '{idx: 32'd1, start_addr: 12'h010, end_addr: 12'h020},
    '{idx: 32'd0, start_addr: 12'hF00, end_addr: 12'hFFF}
  };

  // overlapping map
  localparam tb_rule_t [NoRules-1:0] map_1 = '{
    '{idx: 32'd0, start_addr: 12'h000, end_addr: 12'h010},
    '{idx: 32'd1, start_addr: 12'h00D, end_addr: 12'h020},
    '{idx: 32'd1, start_addr: 12'h100, end_addr: 12'hFFF}
  };

  // DUT signal definitions
  addr_t                  addr;     // input address
  tb_rule_t [NoRules-1:0] addr_map; // input address map
  idx_t                   idx;      // output index
  logic                   dec_valid, dec_error; // output flags
  logic                   en_default_idx; // default enable
  idx_t                   default_idx;    // default index

  longint unsigned passed_checks = 0;
  longint unsigned failed_checks = 0;

  // application of stimuli
  initial begin : stimulus
    passed_checks <= 0;
    failed_checks <= 0;
    addr_map       <= map_0;
    en_default_idx <= 1'b0;
    default_idx    <= idx_t'(1);
    #500;

    // count over all addresses
    $info("Start address application");
    for (int i = 0; i < 2**AddrWidth; i++) begin
      addr <= addr_t'(i);
      #1;
    end

    $info("Change addr map to an overlapping one expect warning");
    addr_map <= map_1;
    #100;
    $info("Change addr map back and enable default decode to idx 1");
    addr_map       <= map_0;
    en_default_idx <= 1'b1;
    #100;

    // count over all addresses
    for (int i = 0; i < 2**AddrWidth; i++) begin
      addr <= addr_t'(i);
      #1;
    end
    #500

    $info("Finished Simulation");
    $display("Passed: %d", passed_checks);
    $display("Failed: %d", failed_checks);
    $stop();
  end

  // checker assertions, these assertion get triggered every time the input address changes
  // serves as model for the address decoder
  always @(addr) #0 begin : proc_check_decode
    for (int unsigned i = 0; i < NoRules; i++) begin
      if ((addr >= addr_map[i].start_addr) && (addr < addr_map[i].end_addr )) begin
        // decode should pass
        check_decode: assert (idx == addr_map[i].idx) passed_checks++; else begin
            failed_checks++;
            $warning("Decoder did not decode correctly.");
        end
        check_valid: assert (dec_valid == 1'b1 && dec_error == 1'b0) passed_checks++; else begin
            failed_checks++;
            $warning("Unexpected decode flag on assumed valid decode.");
        end
      end else begin
        // check for the right decode error
        if (dec_valid == 1'b0) begin
          if (en_default_idx) begin
            check_default: assert (default_idx == idx) passed_checks++; else begin
              failed_checks++;
              $warning("Enabled default index, however wrong default decoding.");
            end
            check_flags: assert (dec_error == 1'b0) passed_checks++; else begin
              failed_checks++;
              $warning("Unexpected decode flags on default decode enabled.");
            end
          end else begin
            check_error: assert (dec_error == 1'b1) passed_checks++; else begin
              failed_checks++;
              $warning("Unexpected decode flags on assumed decode error.");
            end
          end
        end
      end
    end
  end

  // DUT instantiation
  addr_decode #(
    .NoIndices ( NoIndices ), // number indices in rules
    .NoRules   ( NoRules   ), // total number of rules
    .addr_t    ( addr_t    ), // address type
    .rule_t    ( tb_rule_t )  // has to be overridden, see above!
  ) i_addr_decode_dut (
    .addr_i          ( addr           ), // address to decode
    .addr_map_i      ( addr_map       ), // address map: rule with the highest position wins
    .idx_o           ( idx            ), // decoded index
    .dec_valid_o     ( dec_valid      ), // decode is valid
    .dec_error_o     ( dec_error      ), // decode is not valid
    // Default index mapping enable
    .en_default_idx_i( en_default_idx ), // enable default port mapping
    .default_idx_i   ( default_idx    )  // default port index
  );
endmodule

