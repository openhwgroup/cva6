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

// Address Decoder: Maps the input address combinatorially to an index.
// The address map `addr_map_i` is a packed array of rule_t structs.
// The ranges of any two rules may overlap. If so, the rule at the higher (more significant)
// position in `addr_map_i` prevails.
//
// The address decoder expects three fields in `rule_t`:
//
// typedef struct packed {
//   int unsigned idx;
//   addr_t       start_addr;
//   addr_t       end_addr;
// } rule_t;
//
//  - `idx`:        index of the rule, has to be < `NoIndices`
//  - `start_addr`: start address of the range the rule describes, value is included in range
//  - `end_addr`:   end address of the range the rule describes, value is NOT included in range
//
// There can be an arbitrary number of address rules. There can be multiple
// ranges defined for the same index. The start address has to be less than the end address.
//
// There is the possibility to add a default mapping:
// `en_default_idx_i`: Driving this port to `1'b1` maps all input addresses
// for which no rule in `addr_map_i` exists to the default index specified by
// `default_idx_i`. In this case, `dec_error_o` is always `1'b0`.
//
// Assertions: The module checks every time there is a change in the address mapping
// if the resulting map is valid. It fatals if `start_addr` is higher than `end_addr`
// or if a mapping targets an index that is outside the number of allowed indices.
// It issues warnings if the address regions of any two mappings overlap.

module addr_decode #(
  parameter int unsigned NoIndices = 32'd0, // number indices in rules
  parameter int unsigned NoRules   = 32'd0, // total number of rules
  parameter type         addr_t    = logic, // address type
  parameter type         rule_t    = logic, // has to be overridden, see above!
  // DEPENDENT PARAMETERS DO NOT OVERWRITE!
  parameter int unsigned IdxWidth  = (NoIndices > 32'd1) ? $clog2(NoIndices) : 32'd1,
  parameter type         idx_t     = logic [IdxWidth-1:0]
) (
  input  addr_t               addr_i,           // address to decode
  input  rule_t [NoRules-1:0] addr_map_i,       // address map: rule with the highest position wins
  output idx_t                idx_o,            // decoded index
  output logic                dec_valid_o,      // decode is valid
  output logic                dec_error_o,      // decode is not valid
  // Default index mapping enable
  input  logic                en_default_idx_i, // enable default port mapping
  input  idx_t                default_idx_i     // default port index
);

  logic [NoRules-1:0] matched_rules; // purely for address map debugging

  always_comb begin
    // default assignments
    matched_rules = '0;
    dec_valid_o   = 1'b0;
    dec_error_o   = (en_default_idx_i) ? 1'b0 : 1'b1;
    idx_o         = (en_default_idx_i) ? default_idx_i : '0;

    // match the rules
    for (int unsigned i = 0; i < NoRules; i++) begin
      if ((addr_i >= addr_map_i[i].start_addr) && (addr_i < addr_map_i[i].end_addr)) begin
        matched_rules[i] = 1'b1;
        dec_valid_o      = 1'b1;
        dec_error_o      = 1'b0;
        idx_o            = idx_t'(addr_map_i[i].idx);
      end
    end
  end

  // Assumptions and assertions
  `ifndef VERILATOR
  // pragma translate_off
  initial begin : proc_check_parameters
    assume ($bits(addr_i) == $bits(addr_map_i[0].start_addr)) else
      $warning($sformatf("Input address has %d bits and address map has %d bits.",
        $bits(addr_i), $bits(addr_map_i[0].start_addr)));
    assume (NoRules > 0) else
      $fatal(1, $sformatf("At least one rule needed"));
    assume (NoIndices > 0) else
      $fatal(1, $sformatf("At least one index needed"));
  end

  assert final ($onehot0(matched_rules)) else
    $warning("More than one bit set in the one-hot signal, matched_rules");

  // These following assumptions check the validity of the address map.
  // The assumptions gets generated for each distinct pair of rules.
  // Each assumption is present two times, as they rely on one rules being
  // effectively ordered. Only one of the rules with the same function is
  // active at a time for a given pair.
  // check_start:        Enforces a smaller start than end address.
  // check_idx:          Enforces a valid index in the rule.
  // check_overlap:      Warns if there are overlapping address regions.
  always @(addr_map_i) #0 begin : proc_check_addr_map
    if (!$isunknown(addr_map_i)) begin
      for (int unsigned i = 0; i < NoRules; i++) begin
        check_start : assume (addr_map_i[i].start_addr < addr_map_i[i].end_addr) else
          $fatal(1, $sformatf("This rule has a higher start than end address!!!\n\
              Violating rule %d.\n\
              Rule> IDX: %h START: %h END: %h\n\
              #####################################################",
              i ,addr_map_i[i].idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr));
        // check the SLV ids
        check_idx : assume (addr_map_i[i].idx < NoIndices) else
            $fatal(1, $sformatf("This rule has a IDX that is not allowed!!!\n\
            Violating rule %d.\n\
            Rule> IDX: %h START: %h END: %h\n\
            Rule> MAX_IDX: %h\n\
            #####################################################",
            i, addr_map_i[i].idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr,
            (NoIndices-1)));
        for (int unsigned j = i + 1; j < NoRules; j++) begin
          // overlap check
          check_overlap : assume (!((addr_map_i[j].start_addr < addr_map_i[i].end_addr) &&
                                    (addr_map_i[j].end_addr > addr_map_i[i].start_addr)))   else
               $warning($sformatf("Overlapping address region found!!!\n\
              Rule %d: IDX: %h START: %h END: %h\n\
              Rule %d: IDX: %h START: %h END: %h\n\
              #####################################################",
              i, addr_map_i[i].idx, addr_map_i[i].start_addr, addr_map_i[i].end_addr,
              j, addr_map_i[j].idx, addr_map_i[j].start_addr, addr_map_i[j].end_addr));
        end
      end
    end
  end
  // pragma translate_on
  `endif
endmodule
