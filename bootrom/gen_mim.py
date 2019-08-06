# python tcl/bmm_gen.py search-bram.log boot/boot.bmm 256 65536

from string import Template
import sys
import re

# check arguments
if len(sys.argv) != 4:
  print("Wrong arguments\nbmm_gen [in] [out]")
  exit()

# read the ramb search result
f = open(sys.argv[1], "r")
lines = f.readlines()
f.close()

bram_locs = []
                      
for i, line in enumerate(lines):
  ram_match = re.match(r"i_bootrom/addr_q_reg_?[a-z]* BUSWIDTH PLACED = RAMB\d+_(X\d+Y\d+)", line)
  if ram_match:
    bram_locs.append(ram_match.group(1))

mim = """\
<?xml version="1.0" encoding="UTF-8"?>
<MemInfo Version="1" Minor="5">
  <Processor Endianness="Little" InstPath="i_bootrom">
    <AddressSpace Name="i_bootrom" Begin="0" End="8191">
      <BusBlock>
        <BitLane MemType="RAMB36" Placement="$contentL">        
          <DataWidth MSB="31" LSB="0"/>
          <AddressRange Begin="0" End="8191"/>
          <Parity ON="false" NumBits="0"/>
        </BitLane>
        <BitLane MemType="RAMB36" Placement="$contentH">        
          <DataWidth MSB="63" LSB="32"/>
          <AddressRange Begin="0" End="8191"/>
          <Parity ON="false" NumBits="0"/>
        </BitLane>
      </BusBlock>
    </AddressSpace>
  </Processor>
  <Config>
    <Option Name="Part" Val="$part"/>
  </Config>
  <DRC>
    <Rule Name="RDADDRCHANGE" Val="false"/>
  </DRC>
</MemInfo>
"""

""" Generate mim file for bootcode update
"""
with open(sys.argv[3], "w") as f:
  s = Template(mim)
  f.write(s.substitute(contentL=bram_locs[1], contentH=bram_locs[0], part=sys.argv[2]))
  f.close()