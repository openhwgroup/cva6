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

open_hw_manager

connect_hw_server -url localhost:3121

if {$::env(BOARD) eq "genesys2"} {
  set device_name xc7k325t_0
} elseif {$::env(BOARD) eq "vc707"} {
  set device_name xc7vx485t_0
} elseif {$::env(BOARD) eq "kc705"} {
  set device_name xc7k325t_0
} elseif {$::env(BOARD) eq "nexys_video"} {
  set device_name xc7a200t_0
} else {
  puts "ERROR: Unknown BOARD=$::env(BOARD)"
  exit 1
}

# Auto-detect the hardware target containing our device
foreach target [get_hw_targets] {
  open_hw_target $target
  if {[llength [get_hw_devices $device_name]] > 0} {
    break
  }
  close_hw_target
}

current_hw_device [get_hw_devices $device_name]
set_property PROGRAM.FILE {work-fpga/ariane_xilinx.bit} [current_hw_device]
program_hw_devices [current_hw_device]
refresh_hw_device [current_hw_device]
