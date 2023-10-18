// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Moritz Schneider, ETH Zurich
// Date: 2.10.2019
// Description: 

package tb_pkg;

  class P #(
      parameter WIDTH   = 32,
      parameter PMP_LEN = 32
  );
    static function logic [PMP_LEN-1:0] base_to_conf(logic [WIDTH-1:0] base, int unsigned size_i);
      logic [PMP_LEN-1:0] pmp_reg;

      pmp_reg = '0;
      for (int i = 0; i < WIDTH - 2 && i < PMP_LEN; i++) begin
        if (i + 3 > size_i) begin
          pmp_reg[i] = base[i+2];
        end else if (i + 3 == size_i) begin
          pmp_reg[i] = 1'b0;
        end else begin
          pmp_reg[i] = 1'b1;
        end
      end

      return pmp_reg;
    endfunction
  endclass

endpackage
