class cv32e40x_pma_cfg extends uvm_object;
  pma_region_t regions[$];

  constraint attr_comb_c {
    foreach (regions[i]) {
      regions[i].cacheable == 1'b1 -> regions[i].main   == 1'b1;
      regions[i].main      == 1'b1 -> regions[i].atomic == 1'b1;
    }
  }

  // This variable refers to generated number of regions, not CORE_PARAM_PMA_NUM_REGIONS
  int pma_num_regions               = 0;

  `uvm_object_utils(cv32e40x_pma_cfg)

  function new(string name="cv32e40x_pma_cfg");
    pma_adapted_memory_regions_c pma_memory;
    super.new(name);
    pma_memory = new(CORE_PARAM_PMA_CFG);
    foreach (pma_memory.region[i]) begin
      regions.push_back(pma_memory.region[i].cfg);
      pma_num_regions = pma_num_regions + 1;
    end
  endfunction : new
endclass : cv32e40x_pma_cfg
