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
  localparam CAUSE_LEN = 5;
  localparam PRIV_LEN = 2;  // depends on CPU implementation
  localparam INST_LEN = 32;
  localparam ITYPE_LEN = 3;
  localparam IRETIRE_LEN = 32;
  localparam TIME_LEN = 64;
`ifdef TE_ARCH64  // 64bit arch specific parameters
  localparam XLEN = 64;
`else  // 32bit arch
  localparam XLEN = 64;
`endif

  // struct to save all itypes
  // refer to page 21 of the spec
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
  } itype_e;

  // struct to store data inside the uop FIFO
  typedef struct packed {
    logic                 valid;
    logic [XLEN-1:0]      pc;
    logic [ITYPE_LEN-1:0] itype;       // determined in itype detector
    logic                 compressed;
    logic [PRIV_LEN-1:0]  priv;
  } uop_entry_s;

  // struct to store exc and int infos
  typedef struct packed {
    logic [CAUSE_LEN-1:0] cause;
    logic [XLEN-1:0]      tval;
  } exc_info_s;

  // states definition for FSM
  typedef enum logic {
    IDLE  = 0,
    COUNT = 1
  } state_e;

endpackage
