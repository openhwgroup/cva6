// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface XBAR_TCDM_BUS;

   // REQUEST CHANNEL
   //***************************************
   logic          req;
   logic [31:0]   add;
   logic          wen;
   logic [31:0]   wdata;
   logic [3:0]    be;
   logic          gnt;

   // RESPONSE CHANNEL
   logic         r_opc;
   logic [31:0]  r_rdata;
   logic         r_valid;

   // Master Side
   //***************************************
   modport Master
     (
      output req, output add, output wen, output wdata, output be,
      input gnt, input r_rdata, input r_opc, input r_valid
      );

   // Slave Side
   //***************************************
   modport Slave
     (
      input req, input add, input wen, input wdata, input be,
      output gnt, output r_rdata, output r_opc, output r_valid
      );

endinterface // XBAR_TCDM_BUS
