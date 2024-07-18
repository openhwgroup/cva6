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
# Original Author: Oukalrazqou Abdessamii

<%!
def format_hex(value):
    return f"0x{value:X}"

def format_bool(value):
    return "true" if value else "false"
%>
spike_param_tree:
  bootrom: ${format_bool(spike.bootrom)}
  bootrom_base: ${format_hex(spike.bootrom_base)}
  bootrom_size: ${format_hex(spike.bootrom_size)}
  dram: ${format_bool(spike.dram)}
  dram_base: ${format_hex(spike.dram_base)}
  dram_size: ${format_hex(spike.dram_size)}
  generic_core_config: ${format_bool(spike.generic_core_config)}
  max_steps: ${spike.max_steps}
  max_steps_enabled: ${format_bool(spike.max_steps_enabled)}
  isa: ${spike.isa}
  priv: ${spike.priv}
  core_configs:
% for core in spike.core_configs:
    - isa: ${core.isa}
      marchid: ${format_hex(core.marchid)}
      misa_we: ${format_bool(core.misa_we)}
      misa_we_enable: ${format_bool(core.misa_we_enable)}
      misaligned: ${format_bool(core.misaligned)}
      mmu_mode: ${core.mmu_mode}
      mvendorid: ${format_hex(core.mvendorid)}
      pmpaddr0: ${format_hex(core.pmpaddr0)}
      pmpcfg0: ${format_hex(core.pmpcfg0)}
      pmpregions: ${format_hex(core.pmpregions)}
      priv: ${core.priv}
      status_fs_field_we: ${format_bool(core.status_fs_field_we)}
      status_fs_field_we_enable: ${format_bool(core.status_fs_field_we_enable)}
      status_vs_field_we: ${format_bool(core.status_vs_field_we)}
      status_vs_field_we_enable: ${format_bool(core.status_vs_field_we_enable)}
% endfor
