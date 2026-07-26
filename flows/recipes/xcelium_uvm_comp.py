# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

# Please refer to flows/README.md to add target

from pathlib import Path
import shutil
import typer
import yaml
from flows.utils.utils import (
    CompMode,
    TraceMode,
    Cva6Hier,
    autocompletion_target,
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_info,
    print_success,
    print_error,
    print_param_table,
    run_cmd,
)

app = typer.Typer()


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def xcelium_uvm_comp(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    comp_mode: CompMode = typer.Option(CompMode.rtl, help="Hardware compilation mode"),
    trace_mode: TraceMode = typer.Option(TraceMode.notrace, help="Trace mode"),
    tandem_enabled: bool = typer.Option(False, help="Enable spike tandem"),
    stats: bool = typer.Option(False, help="Enable RTL perf tracer"),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Xcelium UVM compilation / elaboration flow
    """
    print_recipe_title("XCELIUM DESIGN ELABORATION", quiet=quiet)

    # Get testbench config
    repo_dir = Path.cwd()
    testbench_cfg = None
    with (repo_dir / "config" / "target" / target / "testbench_cfg.yml").open(
        "r", encoding="utf-8"
    ) as f:
        testbench_cfg = yaml.safe_load(f)
    cva6_hier = Cva6Hier(testbench_cfg["hier"])

    print_param_table(
        {
            "Target": target,
            "Compilation mode": comp_mode.value,
            "Testbench hier": cva6_hier.value,
            "Trace mode": trace_mode.value,
            "Tandem mode enable": tandem_enabled,
            "Perf tracer RTL enable": stats,
        },
        "Options",
        quiet=quiet,
    )

    # Mode dir
    if comp_mode == CompMode.rtl:
        inout_dir = "sim_rtl"
    elif comp_mode == CompMode.coverage:
        inout_dir = "sim_cov"
    elif comp_mode == CompMode.gate_wc_timing:
        inout_dir = "sim_gate_wc_timing"
    elif comp_mode == CompMode.gate_wc_power:
        inout_dir = "sim_gate_wc_power"
    else:
        print_error("Unknown comp_mode")
        raise typer.Exit(code=1)

    # Test tools in path
    xrun_path = shutil.which("xrun")
    if xrun_path is not None:
        print_success(f"xrun: {xrun_path}", quiet=quiet)
    else:
        print_error("xrun: Not found")
        raise typer.Exit(code=1)

    # Create files and folder paths
    build_root = repo_dir / "build" / target
    elab_dir = build_root / "elab" / inout_dir
    cov_exclude_list = repo_dir / "verif" / "sim" / "cov-exclude-mod.lst"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean", quiet=quiet)
    try:
        if elab_dir.exists():
            shutil.rmtree(elab_dir)
            print_info(f"remove {elab_dir}", quiet=quiet)
    except Exception as e:
        print_error(f"Clean error : {e}")
        raise typer.Exit(code=1)

    elab_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {elab_dir}", quiet=quiet)

    # ==========================================================
    # ENV VARIABLES (passed to run_cmd only)
    # ==========================================================

    env_vars = {
        "CVA6_REPO_DIR": str(repo_dir),
        "TARGET": target,
        "TARGET_CFG": target,
        "SPIKE_PATH": str(
            repo_dir / "verif" / "core-v-verif" / "vendor" / "riscv" / "riscv-isa-sim"
        ),
        "HPDCACHE_DIR": str(repo_dir / "core" / "cache_subsystem" / "hpdcache"),
        "HPDCACHE_TARGET_CFG": str(
            repo_dir / "core/include/cva6_hpdcache_default_config_pkg.sv"
        ),
        "CVA6_UVMT_DIR": str(repo_dir / "verif/tb/uvmt"),
        "CVA6_CORET_DIR": str(repo_dir / "verif/tb/core"),
        "CVA6_UVMT_PATH": str(repo_dir / "verif/tb/uvmt"),
        "CVA6_UVME_PATH": str(repo_dir / "verif/env/uvme"),
        "CV_CORE_LC": "cva6",
        "CV_CORE_UC": "CVA6",
        "CVA6_TB_DIR": str(repo_dir / "verif/tb/core"),
        "DV_UVMT_PATH": str(repo_dir / "verif/tb/uvmt"),
        "DV_UVME_PATH": str(repo_dir / "verif/env/uvme"),
        "DV_UVML_HRTBT_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_libs/uvml_hrtbt"
        ),
        "DV_UVMA_CORE_CNTRL_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_core_cntrl"
        ),
        "DV_UVMA_RVFI_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_rvfi"
        ),
        "DV_UVMA_ISACOV_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_isacov"
        ),
        "DV_UVMA_CLKNRST_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_clknrst"
        ),
        "DV_UVMA_AXI_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_axi5"
        ),
        "DV_UVMA_CVXIF_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_cvxif"
        ),
        "DV_UVMA_INTERRUPT_PATH": str(repo_dir / "verif/env/uvme/uvma_interrupt"),
        "DV_UVMA_DEBUG_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_debug"
        ),
        "DV_UVMA_OBI_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_obi"
        ),
        "DV_UVMC_RVFI_SCOREBOARD_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_components/uvmc_rvfi_scoreboard/"
        ),
        "DV_UVMC_RVFI_REFERENCE_MODEL_PATH": str(
            repo_dir
            / "verif/core-v-verif/lib/uvm_components/uvmc_rvfi_reference_model/"
        ),
        "DV_UVML_TRN_PATH": str(repo_dir / "verif/core-v-verif/lib/uvm_libs/uvml_trn"),
        "DV_UVML_MEM_PATH": str(repo_dir / "verif/core-v-verif/lib/uvm_libs/uvml_mem"),
        "DV_UVML_LOGS_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_libs/uvml_logs"
        ),
        "DV_UVML_SB_PATH": str(repo_dir / "verif/core-v-verif/lib/uvm_libs/uvml_sb"),
        "DV_UVMA_OBI_MEMORY_PATH": str(
            repo_dir / "verif/core-v-verif/lib/uvm_agents/uvma_obi_memory"
        ),
        "CV_CORE_PKG": str(repo_dir / "verif/core-v-verif/core-v-cores/cva6"),
        "DESIGN_RTL_DIR": str(repo_dir / "verif/core-v-verif/core-v-cores/cva6/rtl"),
        "TBSRC_HOME": str(repo_dir / "verif/core-v-verif/cva6/tb"),
    }

    # Get XCELIUM_HOME
    xcelium_home = shutil.which("xrun")
    if xcelium_home:
        # Get the parent directory (bin) then the parent of that
        xcelium_home = Path(xcelium_home).parent.parent
        env_vars["XCELIUM_HOME"] = str(xcelium_home)
        print_info(f"XCELIUM_HOME: {xcelium_home}", quiet=quiet)
    else:
        print_error("Cannot determine XCELIUM_HOME")
        raise typer.Exit(code=1)

    # ==========================================================
    # CUSTOMIZE WITH OPTIONS
    # ==========================================================

    # FILELIST
    flist = []

    if comp_mode in [CompMode.gate_wc_power, CompMode.gate_wc_timing]:
        flist += [
            repo_dir / "build" / target / "synthesis" / "Flist.libverilog",
            repo_dir / "config" / "target" / target / "Flist.cva6_gate",
        ]
    else:
        flist += [repo_dir / "config" / "target" / target / "Flist.cva6"]

    flist += [
        repo_dir / "verif" / "tb" / "core" / "Flist.cva6_tb",
        repo_dir / "verif" / "tb" / "uvmt" / "uvmt_cva6.flist",
    ]

    if stats:
        flist += [repo_dir / "perf-model" / "rtl_models_trace" / "Flist.perf-model"]

    # INCLUDE DIRS
    incdirs = [
        repo_dir / "verif" / "env" / "uvme",
        repo_dir / "verif" / "tb" / "uvmt",
        Path("${XCELIUM_HOME}")
        / "tools.lnx86"
        / "methodology"
        / "UVM"
        / "CDNS-1.2"
        / "sv"
        / "src",
    ]

    # DEFINES
    defines = [
        "UVM",
        "HPDCACHE_ASSERT_OFF=1",
        f"SPIKE_TANDEM={int(tandem_enabled)}",
        "UVM_NO_DEPRECATED",
    ]

    # XRUN OPTIONS
    options = [
        "-elaborate",
        "-messages",
        "-sv",
        "-64",
        "-uvm",
        "-uvmhome",
        "CDNS-1.2",
        "+UVM_VERBOSITY=UVM_LOW",
        "-timescale",
        "1ns/1ps",
        "-status",
        "-access",
        "+rwc",
        "-xmerror",
        "CUNOTB",
        "-nowarn",
        "CUDEFB",
        "-nowarn",
        "CUSRCH",
        "-warn_multiple_driver",
        "-relax_svbtis",
    ]

    # Disabled warnings
    disabled_warnings = ["BIGWIX", "ZROMCW", "STRINT", "ENUMERR", "SPDUSD", "RNDXCELON"]
    for warn in disabled_warnings:
        options += ["-nowarn", warn]

    # Trace mode (prepare design for debug/tracing)
    # Note: -access +rwc is already added above (line 255-256) for all compilations
    # No additional options needed for trace modes in compilation

    # Comp mode
    if comp_mode == CompMode.rtl:
        pass  # No special options for RTL
    elif comp_mode == CompMode.coverage:
        options += [
            "-coverage",
            "all",
            "-covfile",
            f"{cov_exclude_list}",
        ]
    elif comp_mode == CompMode.gate_wc_timing:
        sdf = repo_dir / "build" / target / "synthesis" / "netlist" / "wc_timing.sdf"
        if cva6_hier == Cva6Hier.obi:
            sdf_hier = (
                "uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.cva6_only_pipeline.i_cva6"
            )
        else:
            sdf_hier = "uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.cva6.i_cva6"
        options += [
            "-sdf_cmd_file",
            "sdf.cmd",
        ]
        # Create SDF command file
        sdf_cmd_file = elab_dir / "sdf.cmd"
        sdf_cmd_file.write_text(
            f'COMPILED_SDF_FILE = "{sdf}",\nSCOPE = :{sdf_hier},\nMTM_CONTROL = "MAXIMUM";'
        )
        print_info(f"Created SDF command file: {sdf_cmd_file}", quiet=quiet)
    elif comp_mode == CompMode.gate_wc_power:
        sdf = repo_dir / "build" / target / "synthesis" / "netlist" / "wc_power.sdf"
        if cva6_hier == Cva6Hier.obi:
            sdf_hier = (
                "uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.cva6_only_pipeline.i_cva6"
            )
        else:
            sdf_hier = "uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.cva6.i_cva6"
        options += [
            "-sdf_cmd_file",
            "sdf.cmd",
        ]
        # Create SDF command file
        sdf_cmd_file = elab_dir / "sdf.cmd"
        sdf_cmd_file.write_text(
            f'COMPILED_SDF_FILE = "{sdf}",\nSCOPE = :{sdf_hier},\nMTM_CONTROL = "MAXIMUM";'
        )
        print_info(f"Created SDF command file: {sdf_cmd_file}", quiet=quiet)

    # ==========================================================
    # BUILD XRUN COMMAND
    # ==========================================================

    xrun_cmd = ["xrun"]
    xrun_cmd += options

    for d in incdirs:
        xrun_cmd += [f"+incdir+{d}"]

    for d in defines:
        xrun_cmd += [f"+define+{d}"]

    for f in flist:
        xrun_cmd += ["-f", str(f)]

    # Add UVM package
    xrun_cmd += [
        "${XCELIUM_HOME}/tools.lnx86/methodology/UVM/CDNS-1.2/sv/src/uvm_pkg.sv",
        "-top",
        "uvmt_cva6_tb",
        "-log",
        "compilation.log",
    ]

    # ==========================================================
    # LAUNCH XRUN COMMAND
    # ==========================================================
    print_step("LAUNCH XRUN", quiet=quiet)

    log_file = elab_dir / "compilation.log"

    run_cmd(
        cmd=xrun_cmd,
        cwd=elab_dir,
        env=env_vars,
        error_patterns=["^xm.*: \\*E", "Error-"],
        warning_patterns=["^xm.*: \\*W", "Warning-"],
        highlight_patterns=["elaboration done"],
        log_file=log_file,
        timeout=1800,
        check=False,
        capture_output=True,
        quiet=quiet,
    )

    # Check if elaboration was successful by looking for snapshot directory
    snapshot_dir = elab_dir / "xcelium.d"

    if not snapshot_dir.exists():
        print_error("Xcelium snapshot not generated")
        raise typer.Exit(code=1)

    if not log_file.exists():
        print_error("Compilation log missing")

    # ==========================================================
    # List
    # ==========================================================
    print_step("Generated files", quiet=quiet)
    gen_files = [snapshot_dir, log_file]

    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}", quiet=quiet)

    print_recipe_end("Completed", quiet=quiet)
