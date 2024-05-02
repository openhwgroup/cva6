# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

#!/usr/bin/python3


def define_blacklist(parameters):

    black_list = {}
    black_list["flush_bp_i"] = ["For any HW configuration", "0"]
    black_list["dtlb_hit_i"] = ["For any HW configuration", "1"]

    black_list["hwpf_base_set_i"] = ["For any HW configuration", "0"]
    black_list["hwpf_base_i"] = ["For any HW configuration", "0"]
    black_list["hwpf_base_o"] = ["For any HW configuration", "0"]
    black_list["hwpf_param_set_i"] = ["For any HW configuration", "0"]
    black_list["hwpf_param_i"] = ["For any HW configuration", "0"]
    black_list["hwpf_param_o"] = ["For any HW configuration", "0"]
    black_list["hwpf_throttle_set_i"] = ["For any HW configuration", "0"]
    black_list["hwpf_throttle_i"] = ["For any HW configuration", "0"]
    black_list["hwpf_throttle_o"] = ["For any HW configuration", "0"]
    black_list["hwpf_status_o"] = ["For any HW configuration", "0"]
    black_list["dcache_cmo_req_i"] = ["For any HW configuration", "0"]
    black_list["dcache_cmo_resp_o"] = ["For any HW configuration", "open"]

    param = "IsRVFI"
    paramvalue = "0"
    if paramvalue == "0":
        black_list["RVFI"] = [f"As {param} = {paramvalue}", "0"]

    param = "DebugEn"
    paramvalue = parameters[param].value
    if paramvalue == False:
        black_list["set_debug_pc_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["set_debug_pc_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["debug_mode_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["debug_mode_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["debug_req_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["single_step_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["single_step_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVH"
    paramvalue = parameters[param].value
    if paramvalue == False:
        black_list["v_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["v_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vfs_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vfs_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hfence_vvma_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hfence_gvma_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["flush_tlb_vvma_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["flush_tlb_gvma_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["flush_tlb_vvma_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["flush_tlb_gvma_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["en_g_translation_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["enable_g_translation_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["en_ld_st_g_translation_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["en_ld_st_g_translation_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["ld_st_v_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["ld_st_v_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["csr_hs_ld_st_inst_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["csr_hs_ld_st_inst_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vs_sum_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vs_sum_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vmxr_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vmxr_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vsatp_ppn_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vsatp_ppn_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vs_asid_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vs_asid_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hgatp_ppn_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hgatp_ppn_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vmid_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vmid_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vtw_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vtw_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hu_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hu_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["ld_st_v_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["tinst_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["tinst_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["csr_hs_ld_st_inst_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["exception_gpaddr_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["exception_tinst_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["exception_gva_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hs_ld_st_inst_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hlvx_inst_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hfence_vvma_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["hfence_gvma_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vmid_to_be_flushed_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["gpaddr_to_be_flushed_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVV"
    paramvalue = parameters[param].value
    if paramvalue == False:
        black_list["vs_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vs_o"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVS"
    paramvalue = parameters[param].value
    if paramvalue == False:
        black_list["en_translation_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["enable_translation_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["enable_translation_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["en_ld_st_translation_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["en_ld_st_translation_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["sum_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["sum_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["satp_ppn_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["satp_ppn_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vaddr_to_be_flushed_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["vaddr_to_be_flushed_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["asid_to_be_flushed_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["asid_to_be_flushed_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["mxr_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["mxr_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["asid_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["asid_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["sfence_vma_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["sfence_vma_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "EnableAccelerator"
    paramvalue = "0"
    if paramvalue == "0":
        black_list["ACC_DISPATCHER"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVF"
    paramvalue = "0"
    if paramvalue == "0":
        black_list["fs_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fs_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["frm_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["frm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_valid_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_ready_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_ready_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_fmt_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_rm_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_valid_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_fmt_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_rm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_frm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_prec_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_trans_id_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_result_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_exception_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["csr_write_fflags_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fflags_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["csr_write_fflags_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fprec_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["dirty_fp_state_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["dirty_fp_state_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["we_fpr_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVA"
    paramvalue = parameters[param].value
    if paramvalue == False:
        black_list["amo_req_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["amo_resp_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["amo_valid_commit_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["amo_valid_commit_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "PRIV"
    paramvalue = "MachineOnly"
    if paramvalue == "MachineOnly":  # TODO PRIV to be added to RTL parameters
        black_list["ld_st_priv_lvl_o"] = [f"As {param} = {paramvalue}", "MAchineMode"]
        black_list["ld_st_priv_lvl_i"] = [f"As {param} = {paramvalue}", "MAchineMode"]
        black_list["priv_lvl_o"] = [f"As {param} = {paramvalue}", "MachineMode"]
        black_list["priv_lvl_i"] = [f"As {param} = {paramvalue}", "MachineMode"]
        black_list["tvm_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["tvm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["tw_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["tw_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["tsr_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["tsr_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "PerfCounterEn"
    paramvalue = "0"
    if paramvalue == "0":  # TODO PerfCounterEn to be added to RTL parameters
        black_list["PERF_COUNTERS"] = [f"As {param} = {paramvalue}", "0"]

    param = "FenceEn"
    paramvalue = "0"
    if paramvalue == "0":  # TODO FenceEn to be added to RTL parameters
        black_list["fence_i_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fence_i_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fence_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fence_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "MMUPresent"
    paramvalue = "0"
    if paramvalue == "0":  # TODO the MMUPresent to be added to RTL parameters
        black_list["flush_tlb_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["flush_tlb_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["dtlb_ppn_i"] = [f"As {param} = {paramvalue}", "0"]

    return black_list
