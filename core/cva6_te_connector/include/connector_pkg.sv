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
// Maxime COLSON, Thales

package connector_pkg;
  // These parameters could be used in the ENCODER stage
  localparam CAUSE_LEN = 5;  //Size is ecause_width_p in the E-Trace SPEC
  localparam ITYPE_LEN = 3;  //Size is itype_width_p in the E-Trace SPEC (3 or 4)
  localparam IRETIRE_LEN = 32;  //Size is iretire_width_p in the E-Trace SPEC
  //localparam TIME_LEN = 64; //rvfi_csr used logic [63:0] cycle_q but TIME_LEN could be used in the ENCODER stage

  // struct to save all itypes
  // refer to page 21 of the spec
  // The enum could be used in the ENCODER stage
  typedef enum logic [ITYPE_LEN-1:0] {
    STD = 0,  // none of the other named itype codes
    EXC = 1,  // exception
    INT = 2,  // interrupt
    ERET = 3,  // exception or interrupt return
    NTB = 4,  // nontaken branch
    TB = 5,  // taken branch
    UIJ = 6,  // uninferable jump if ITYPE_LEN == 3, otherwise reserved
    RES = 7  /*, // reserved
    UC = 8, // uninferable call
    IC = 9, // inferable call
    UIJ = 10, // uninferable jump
    IJ = 11, // inferable jump
    CRS = 12, // co-routine swap
    RET = 13, // return
    OUIJ = 14, // other uninferable jump
    OIJ = 15*/  // other inferable jump
  } itype_t;

endpackage
