// Licensed under the Solderpad Hardware License v 2.1 (the “License”); you may not use this file 
// except in compliance with the License, or, at your option, the Apache License version 2.0. You 
// may obtain a copy of the License at

// https://solderpad.org/licenses/SHL-2.1/

// Unless required by applicable law or agreed to in writing, any work distributed under the 
// License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, 
// either express or implied. See the License for the specific language governing permissions and 
// limitations under the License.

// Author:  Umberto Laghi
// Contact: umberto.laghi@studio.unibo.it
// Github:  @ubolakes
// Contributors: 
// Darshak Sheladiya, SYSGO GmbH
// Maxime COLSON, Thales CDI France

/* ITYPE DETECTOR */
/*
it produces the type of the instruction
*/

module itype_detector #(
    parameter ITYPE_LEN = 3  //Size is itype_width_p in the E-Trace SPEC (3 or 4)
) (
    input  logic             valid_i,
    input  logic             exception_i,
    input  logic             interrupt_i,
    input  ariane_pkg::fu_op op_i,
    input  logic             branch_taken_i,
    output iti_pkg::itype_t  itype_o
);

  // internal signals
  logic exception;
  logic interrupt;
  logic eret;
  logic nontaken_branch;
  logic taken_branch;
  logic updiscon;

  // assignments
  assign exception = exception_i;
  assign interrupt = interrupt_i;  // no need to have an inst committed




  assign eret = op_i inside {ariane_pkg::MRET, ariane_pkg::SRET, ariane_pkg::DRET};

  assign nontaken_branch = (  op_i == ariane_pkg::EQ ||
                                op_i == ariane_pkg::NE ||
                                op_i == ariane_pkg::LTS ||
                                op_i == ariane_pkg::GES ||
                                op_i == ariane_pkg::LTU ||
                                op_i == ariane_pkg::GEU) &&
                                 ~branch_taken_i;

  assign taken_branch = ( op_i == ariane_pkg::EQ ||
                            op_i == ariane_pkg::NE ||
                            op_i == ariane_pkg::LTS ||
                            op_i == ariane_pkg::GES ||
                            op_i == ariane_pkg::LTU ||
                            op_i == ariane_pkg::GEU) &&
                            branch_taken_i;

  assign updiscon = op_i == ariane_pkg::JALR;

  // assigning the itype
  always_comb begin
    // initialization
    itype_o = iti_pkg::STANDARD;

    if (exception) begin  // exception
      itype_o = iti_pkg::EXC;
    end else if (interrupt) begin  // interrupt
      itype_o = iti_pkg::INT;
    end else if (valid_i) begin
      if (eret) begin  // exception or interrupt return
        itype_o = iti_pkg::ERET;
      end else if (nontaken_branch) begin  // nontaken branch
        itype_o = iti_pkg::NON_TAKEN_BR;
      end else if (taken_branch) begin  // taken branch
        itype_o = iti_pkg::TAKEN_BR;
      end else if (ITYPE_LEN == 3 && updiscon) begin  // uninferable discontinuity
        itype_o = iti_pkg::UNINF_JMP;
      end
    end
  end

endmodule
