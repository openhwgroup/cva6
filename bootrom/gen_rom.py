#!/usr/bin/env python3

from string import Template
import argparse
import os.path
import sys

parser = argparse.ArgumentParser(description='Convert binary file to verilog rom')
parser.add_argument('filename', metavar='filename', nargs=1,
                   help='filename of input binary')

args = parser.parse_args()
file = args.filename[0];

# check that file exists
if not os.path.isfile(file):
    print("File {} does not exist.".format(filename))
    sys.exit(1)

filename = os.path.splitext(file)[0]

license = """\
/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File: $filename.v
 *
 * Description: Auto-generated bootrom
 */

// Auto-generated code
"""

module = """\
module $filename (
   input  logic         clk_i,
   input  logic         req_i,
   input  logic [63:0]  addr_i,
   output logic [63:0]  rdata_o
);
    localparam int RomSize = $size;

    const logic [RomSize-1:0][63:0] mem = {
        $content
    };

    logic [$$clog2(RomSize)-1:0] addr_q;

    always_ff @(posedge clk_i) begin
        if (req_i) begin
            addr_q = addr_i[$$clog2(RomSize)-1+3:3];
        end
    end

    assign rdata_o = mem[addr_q];
endmodule
"""

rom = []

with open(filename + ".img", "rb") as f:
    byte = True;
    while byte:
        word = ""
        # read 64-bit a.k.a 8 byte
        for i in range(0, 8):
            byte = f.read(1)
            if i == 4:
                word = "_" + word
            if byte:
                word = byte.hex() + word
            # fill up with zeros if unaligned
            else:
                pass
                # word += "00";

        if word != "_":
            word = "64'h" + word
            # print(word)
            rom.append(word)
    f.close()


rom.reverse()

# open file for writing
with open(filename + ".sv", "w") as f:

    # some string preparations
    rom_str = ""
    i = 0
    for r in rom:
        i += 1
        rom_str += r + ",\n        ";

    rom_str.rstrip()
    # strip the last whitespace
    rom_str = rom_str[:-10]

    # write files
    f.write(license)
    s = Template(module)
    f.write(s.substitute(filename=filename, size=i, content=rom_str))

    f.close()
