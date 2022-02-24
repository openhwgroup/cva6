//
// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
//

class cv32e40s_pma_cfg extends uvm_object;
  pma_region_t regions[$];

  constraint attr_comb_c {
    foreach (regions[i]) {
      regions[i].cacheable == 1'b1 -> regions[i].main   == 1'b1;
    }
  }

  // This variable refers to generated number of regions, not CORE_PARAM_PMA_NUM_REGIONS
  int pma_num_regions               = 0;

  `uvm_object_utils(cv32e40s_pma_cfg)

  function new(string name="cv32e40s_pma_cfg");
    pma_adapted_memory_regions_c pma_memory;
    super.new(name);
    pma_memory = new(CORE_PARAM_PMA_CFG);
    foreach (pma_memory.region[i]) begin
      regions.push_back(pma_memory.region[i].cfg);
      pma_num_regions = pma_num_regions + 1;
    end
  endfunction : new
endclass : cv32e40s_pma_cfg
