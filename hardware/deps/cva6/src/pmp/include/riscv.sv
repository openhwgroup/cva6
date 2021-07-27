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
// Description: PMP package

package riscv;
    // --------------------
    // Privilege Spec
    // --------------------
    typedef enum logic[1:0] {
      PRIV_LVL_M = 2'b11,
      PRIV_LVL_S = 2'b01,
      PRIV_LVL_U = 2'b00
    } priv_lvl_t;

    // PMP
    typedef enum logic [1:0] {
        OFF   = 2'b00,
        TOR   = 2'b01,
        NA4   = 2'b10,
        NAPOT = 2'b11
    } pmp_addr_mode_t;

    // PMP Access Type
    typedef enum logic [2:0] {
        ACCESS_NONE  = 3'b000,
        ACCESS_READ  = 3'b001,
        ACCESS_WRITE = 3'b010,
        ACCESS_EXEC  = 3'b100
    } pmp_access_t;

    typedef struct packed {
        logic           x;
        logic           w;
        logic           r;
    } pmpcfg_access_t;

    // packed struct of a PMP configuration register (8bit)
    typedef struct packed {
        logic           locked;     // lock this configuration
        logic [1:0]     reserved;
        pmp_addr_mode_t addr_mode;  // Off, TOR, NA4, NAPOT
        pmpcfg_access_t access_type;
    } pmpcfg_t;

endpackage