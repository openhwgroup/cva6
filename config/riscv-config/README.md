<!--
# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Original Author: Zbigniew CHAMSKI - Thales
-->

# File organization

- `Makefile`: the makefile needed to regenerate the Yaml files using `riscv-config`.
- `TARGET`: directory holding input and output files for configuration named `TARGET` (currently only `cv32a65x`)
  - `spec`: Directory holding input files
    - `isa_spec.yaml`: specification of the ISA, including CSRs and privileges (expressed as canonical extension letters)
    - `custom_spec.yaml`: specification of custom CSRs
    - `platform_spec.yaml`: specification of platform-level values/properties
  - `generated`: Directory holding generated files produced by `riscv-config` from the spec files
    - `isa_gen.yaml`: ISA definition completed y `riscv-config`
    - `custom_gen.yaml`: Custom CSR definitions completed by `riscv-config`
    - `platform_gen.yaml`: Platform-specific values/properties completed by `riscv-config`

# Prerequisites

- Python3 (tested with 3.9 on RedHat Enterprise Linux 8)

# Invocation

From any directory, run

```
make -C <CVA6_top_directory>/config/riscv-config all
```

