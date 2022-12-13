// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


module pad_functional_pd
(
   input  logic             OEN,
   input  logic             I,
   output logic             O,
   input  logic             PEN,
   inout  logic             PAD
);

  (* PULLDOWN = "YES" *)
  IOBUF iobuf_i (
    .T ( OEN ),
    .I ( I    ),
    .O ( O    ),
    .IO( PAD  )
  );

endmodule

module pad_functional_pu
(
   input  logic             OEN,
   input  logic             I,
   output logic             O,
   input  logic             PEN,
   inout  logic             PAD
);

  (* PULLUP = "YES" *)
  IOBUF iobuf_i (
    .T ( OEN ),
    .I ( I    ),
    .O ( O    ),
    .IO( PAD  )
  );

endmodule
