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
    ".bender/git/checkouts/common_cells-*/src/counter.sv",
    ".bender/git/checkouts/common_cells-*/src/cf_math_pkg.sv",
    ".bender/git/checkouts/common_cells-*/src/sync.sv",
    ".bender/git/checkouts/common_cells-*/src/sync_wedge.sv",
    ".bender/git/checkouts/common_cells-*/src/edge_detect.sv",
    ".bender/git/checkouts/tech_cells_generic-*/src/rtl/tc_clk.sv",
    ".bender/git/checkouts/tech_cells_generic-*/src/deprecated/pulp_clk_cells.sv"#,
    # ".bender/git/checkouts/common_cells-*/src/lzc.sv"

]

# static commands
static_addfiles = [
    "project addfile include/te_pkg.sv",
    "project addfile rtl/te_branch_map.sv",
    "project addfile rtl/te_filter.sv",
    "project addfile rtl/te_packet_emitter.sv",
    "project addfile rtl/lzc.sv",
    "project addfile rtl/te_priority.sv",
    "project addfile rtl/te_reg.sv",
    "project addfile rtl/te_resync_counter.sv",
    "project addfile rtl/rv_tracer.sv",
    "project addfile tb/tb_rv_tracer.sv"
]

static_sim_commands = [
    "project compileall",
    "vsim -voptargs=+acc work.tb_rv_tracer",
    "log -r /*",
    "run 200"
]

# write to the .do file
with open(do_filename, "w") as do_file:
    # project creation
    do_file.write("project new . rv_tracer\n")

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