# Copyright 2018 ETH Zurich and University of Bologna.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
# Description: Program Genesys II

open_hw

connect_hw_server -url localhost:3121

if {$::env(BOARD) eq "genesys2"} {
  open_hw_target {localhost:3121/xilinx_tcf/Digilent/200300A8CD43B}

  current_hw_device [get_hw_devices xc7k325t_0]
  set_property PROGRAM.FILE {work-fpga/ariane_xilinx.bit} [get_hw_devices xc7k325t_0]
  program_hw_devices [get_hw_devices xc7k325t_0]
  refresh_hw_device [lindex [get_hw_devices xc7k325t_0] 0]
} elseif {$::env(BOARD) eq "vc707"} {
  open_hw_target {localhost:3121/xilinx_tcf/Digilent/210203A5FC70A}

  current_hw_device [get_hw_devices xc7vx485t_0]
  set_property PROGRAM.FILE {work-fpga/ariane_xilinx.bit} [get_hw_devices xc7vx485t_0]
  program_hw_devices [get_hw_devices xc7vx485t_0]
  refresh_hw_device [lindex [get_hw_devices xc7vx485t_0] 0]
} else {
      exit 1
}
