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
    black_list["flush_bp_i"] = ["For any HW configuration", "zero"]

    param = "IsRVFI"
    paramvalue = "0"
    if paramvalue == "0":
        black_list["RVFI"] = [f"As {param} = {paramvalue}", "0"]

    param = "DebugEn"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["set_debug_pc_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["debug_mode_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["debug_req_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVV"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["vs_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "EnableAccelerator"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["ACC_DISPATCHER"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVF"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["fs_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["frm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_valid_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_ready_o"] = [f"As {param} = {paramvalue}", "0"]
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

    param = "RVA"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["amo_req_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["amo_resp_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["amo_valid_commit_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "PRIV"
    paramvalue = "MachineOnly"
    if paramvalue == "MachineOnly":  # TODO PRIV to be added to RTL parameters
        black_list["ld_st_priv_lvl_i"] = [f"As {param} = {paramvalue}", "MAchineMode"]
        black_list["priv_lvl_i"] = [f"As {param} = {paramvalue}", "MachineMode"]
        # black_list["tvm_i"] = [f"As {param} = {paramvalue}", "0"]
        # black_list["tw_i"] = [f"As {param} = {paramvalue}", "0"]
        # black_list["tsr_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "PerfCounterEn"
    paramvalue = "0"
    if paramvalue == "0":  # TODO PerfCounterEn to be added to RTL parameters
        black_list["PERF_COUNTERS"] = [f"As {param} = {paramvalue}", "0"]

    param = "MMUPresent"
    paramvalue = "0"
    if paramvalue == "0":  # TODO the MMUPresent to be added to RTL parameters
        black_list["flush_tlb_i"] = [f"As {param} = {paramvalue}", "0"]

    return black_list
