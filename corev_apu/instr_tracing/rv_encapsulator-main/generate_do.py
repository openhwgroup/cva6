# Copyright (C) 2025 ETH Zurich and University of Bologna

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#      http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# SPDX-License-Identifier: Apache-2.0

# Author:  Umberto Laghi
# Contact: umberto.laghi2@unibo.it
# Github:  @ubolakes

import glob

# output .do file
do_filename = "addfiles.do"

# glob patterns for dynamic files
dynamic_patterns = [
    ".bender/git/checkouts/common_cells-*/src/counter.sv"
]

# static commands
static_addfiles = [
    "project addfile src/include/encap_pkg.sv",
    "project addfile src/rtl/fifo_v3.sv",
    "project addfile src/rtl/atb_transmitter.sv",
    "project addfile src/rtl/encapsulator.sv",
    "project addfile src/rtl/slicer.sv",
    "project addfile src/rtl/rv_encapsulator.sv",
    "project addfile tb/tb_rv_encapsulator.sv"
]

static_sim_commands = [
    "project compileall",
    "vsim -voptargs=+acc work.tb_rv_encapsulator",
    "log -r /*",
    "run 200"
]

# write to the .do file
with open(do_filename, "w") as do_file:
    # project creation
    do_file.write("project new . encapsulator\n")

    # dynamic addfile entries
    for pattern in dynamic_patterns:
        for filepath in glob.glob(pattern):
            filepath = filepath.replace("\\", "/")  # Normalize path
            do_file.write(f"project addfile {filepath}\n")

    # static addfile entries
    for cmd in static_addfiles:
        do_file.write(f"{cmd}\n")

    # simulation and run commands
    for cmd in static_sim_commands:
        do_file.write(f"{cmd}\n")