//-----------------------------------------------------------------------------

// Title         : test random vectors for a few different input widths
//-----------------------------------------------------------------------------
// File          : popcount_tb.sv
// Author        : Manuel Eggimann <meggimann@iis.ee.ethz.ch>
//-----------------------------------------------------------------------------
// Description :
// Tests a few different instantiations of popcount with random vectors
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
// Copyright (C) 2013-2018 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//-----------------------------------------------------------------------------

`define SV_RAND_CHECK(r) \
do begin \
  if (!(r)) begin \
    $display("%s:%0d: Randomization failed \"%s\"", `__FILE__, `__LINE__, `"r`"); \
    $finish;\
  end\
end while (0)

module popcount_tb;

   //---------------- Signals connecting to MUT ----------------
   logic [4:0] data_w5;
   logic [3:0] popcount_w5;

   logic [15:0] data_w16;
   logic [4:0]  popcount_w16;

   logic [31:0] data_w32;
   logic [5:0] popcount_w32;

   logic [63:0] data_w64;
   logic [6:0]  popcount_w64;

   logic [980:0] data_w981;
   logic [10:0]  popcount_w981;

   //--------------------- Instantiate MUT ---------------------
   popcount #(.INPUT_WIDTH(5)) i_popcount_w5
     (.data_i(data_w5),
      .popcount_o(popcount_w5));

   popcount #(.INPUT_WIDTH(16)) i_popcount_w16
     (.data_i(data_w16),
      .popcount_o(popcount_w16));

   popcount #(.INPUT_WIDTH(32)) i_popcount_w32
     (.data_i(data_w32),
      .popcount_o(popcount_w32));

   popcount #(.INPUT_WIDTH(64)) i_popcount_w64
     (.data_i(data_w64),
      .popcount_o(popcount_w64));

   popcount #(.INPUT_WIDTH(981)) i_popcount_w981
     (.data_i(data_w981),
      .popcount_o(popcount_w981));

   //---------------------- Test Procedure ----------------------

   initial begin
     //------------------------------------------------------------
     //Test 12 bit popcount
     data_w5    = 0;
     #5ns;
     assert(popcount_w5 == $countones(data_w5)) else $error("Popcount of %b was %d but should be %d.", data_w5, popcount_w5, $countones(data_w5));
     data_w5    = 1;
     #5ns;
     assert(popcount_w5 == $countones(data_w5)) else $error("Popcount of %b was %d but should be %d.", data_w5, popcount_w5, $countones(data_w5));
     data_w5    = '1;
     #5ns;
     assert(popcount_w5 == $countones(data_w5)) else $error("Popcount of %b was %d but should be %d.", data_w5, popcount_w5, $countones(data_w5));

     for(int i = 0; i<100; i++)
       begin
         `SV_RAND_CHECK(randomize(data_w5));
         #5ns;
         assert(popcount_w5 == $countones(data_w5)) else $error("Popcount of %b was %d but should be %d.", data_w5, popcount_w5, $countones(data_w5));
       end

     //Test 16 bit popcount
     data_w16    = 0;
     #5ns;
     assert(popcount_w16 == $countones(data_w16)) else $error("Popcount of %b was %d but should be %d.", data_w16, popcount_w16, $countones(data_w16));
     data_w16    = 1;
     #5ns;
     assert(popcount_w16 == $countones(data_w16)) else $error("Popcount of %b was %d but should be %d.", data_w16, popcount_w16, $countones(data_w16));
     data_w16    = '1;
     #5ns;
     assert(popcount_w16 == $countones(data_w16)) else $error("Popcount of %b was %d but should be %d.", data_w16, popcount_w16, $countones(data_w16));
     for(int i = 0; i<100; i++)
       begin
         `SV_RAND_CHECK(randomize(data_w16));
         #5ns;
         assert(popcount_w16 == $countones(data_w16)) else $error("Popcount of %b was %d but should be %d.", data_w16, popcount_w16, $countones(data_w16));
       end

     //Test 32 bit popcount
     data_w32    = 0;
     #5ns;
     assert(popcount_w32 == $countones(data_w32)) else $error("Popcount of %b was %d but should be %d.", data_w32, popcount_w32, $countones(data_w32));
     data_w32    = 1;
     #5ns;
     assert(popcount_w32 == $countones(data_w32)) else $error("Popcount of %b was %d but should be %d.", data_w32, popcount_w32, $countones(data_w32));
     data_w32    = '1;
     #5ns;
     assert(popcount_w32 == $countones(data_w32)) else $error("Popcount of %b was %d but should be %d.", data_w32, popcount_w32, $countones(data_w32));
     for(int i = 0; i<100; i++)
       begin
         `SV_RAND_CHECK(randomize(data_w32));
         #5ns;
         assert(popcount_w32 == $countones(data_w32)) else $error("Popcount of %b was %d but should be %d.", data_w32, popcount_w32, $countones(data_w32));
       end

     //Test 64 bit popcount
     data_w64    = 0;
     #5ns;
     assert(popcount_w64 == $countones(data_w64)) else $error("Popcount of %b was %d but should be %d.", data_w64, popcount_w64, $countones(data_w64));
     data_w64    = 1;
     #5ns;
     assert(popcount_w64 == $countones(data_w64)) else $error("Popcount of %b was %d but should be %d.", data_w64, popcount_w64, $countones(data_w64));
     data_w64    = '1;
     #5ns;
     assert(popcount_w64 == $countones(data_w64)) else $error("Popcount of %b was %d but should be %d.", data_w64, popcount_w64, $countones(data_w64));
     for(int i = 0; i<100; i++)
       begin
         `SV_RAND_CHECK(randomize(data_w64));
         #5ns;
         assert(popcount_w64 == $countones(data_w64)) else $error("Popcount of %b was %d but should be %d.", data_w64, popcount_w64, $countones(data_w64));
       end

     //Test 981 bit popcount
     data_w981    = 0;
     #5ns;
     assert(popcount_w981 == $countones(data_w981)) else $error("Popcount of %b was %d but should be %d.", data_w981, popcount_w981, $countones(data_w981));
     data_w981    = 1;
     #5ns;
     assert(popcount_w981 == $countones(data_w981)) else $error("Popcount of %b was %d but should be %d.", data_w981, popcount_w981, $countones(data_w981));
     data_w981    = '1;
     #5ns;
     assert(popcount_w981 == $countones(data_w981)) else $error("Popcount of %b was %d but should be %d.", data_w981, popcount_w981, $countones(data_w981));
     for(int i = 0; i<100; i++)
       begin
         `SV_RAND_CHECK(randomize(data_w981));
         #5ns;
         assert(popcount_w981 == $countones(data_w981)) else $error("Popcount of %b was %d but should be %d.", data_w981, popcount_w981, $countones(data_w981));
       end

     //------------------------------------------------------------
   end

endmodule : popcount_tb
