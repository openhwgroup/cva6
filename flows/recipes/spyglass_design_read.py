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
from flows.utils.manifest import write_manifest
from flows.utils.utils import (
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
    print_code,
)

app = typer.Typer()


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def spyglass_design_read(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Spyglass design read
    """
    print_recipe_title("Spyglass design read", quiet=quiet)

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
            "Testbench hier": cva6_hier.value,
        },
        "Options",
        quiet=quiet,
    )

    # Test tools in path
    aipk_read_path = shutil.which("aipk_read")
    if aipk_read_path is not None:
        print_success(f"aipk_read: {aipk_read_path}", quiet=quiet)
    else:
        print_error("aipk_read: Not found", quiet=quiet)
        raise typer.Exit(code=1)

    # Testbench selection
    if cva6_hier == Cva6Hier.obi:
        top_elaborate = "cva6_example_obi"
    elif cva6_hier == Cva6Hier.axi:
        top_elaborate = "cva6_example_axi"
    else:
        print_error("Unknown cva6_hier", quiet=quiet)
        raise typer.Exit(code=1)

    # Create files and folder paths
    build_root = repo_dir / "build" / target
    spyglass_dir = build_root / "spyglass"
    sg_setup_dir = spyglass_dir / "sg_setup" / top_elaborate
    tmp_dir = spyglass_dir / "tmp"

    options_file = sg_setup_dir / f"{top_elaborate}_options.tcl"
    goals_file = sg_setup_dir / f"{top_elaborate}_goals_setup.tcl"
    waiver_file = sg_setup_dir / f"{top_elaborate}_waiver.awl"
    sgdc_file = sg_setup_dir / f"{top_elaborate}.sgdc"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean", quiet=quiet)
    try:
        if spyglass_dir.exists():
            shutil.rmtree(spyglass_dir)
            print_info(f"remove {spyglass_dir}", quiet=quiet)
    except Exception as e:
        print_error(f"Clean error : {e}", quiet=quiet)
        raise typer.Exit(code=1)

    sg_setup_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {sg_setup_dir}", quiet=quiet)

    tmp_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {tmp_dir}", quiet=quiet)

    # ==========================================================
    # ENV VARIABLES (passed to run_cmd only)
    # ==========================================================

    env_vars = {
        "CVA6_REPO_DIR": str(repo_dir),
        "TARGET_CFG": target,
        "HPDCACHE_DIR": str(repo_dir / "core" / "cache_subsystem" / "hpdcache"),
        "HPDCACHE_TARGET_CFG": str(
            repo_dir / "core" / "include" / "cva6_hpdcache_default_config_pkg.sv"
        ),
        "SPYGLASS_TMPDIR": str(tmp_dir),
    }

    # ==========================================================
    # CUSTOMIZE WITH OPTIONS
    # ==========================================================

    # FILELIST
    flist = repo_dir / "config" / "target" / target / "Flist.cva6"

    # ==========================================================
    # GENERATE OPTIONS FILE
    # ==========================================================
    print_step("Generate options file", quiet=quiet)

    options_content = """## File Name : Option File
set_option enableSV no
set_option enableSV09 yes
"""

    options_file.write_text(options_content)

    print_info(f"File generated at {options_file}", quiet=quiet)
    print_code(options_content, "tcl", quiet=quiet)

    # ==========================================================
    # GENERATE GOALS SETUP
    # ==========================================================
    print_step("Generate goals setup file", quiet=quiet)

    goals_content = """## File Name : SpyGlass Goal Setup File
set_parameter ignore_bitwiseor_assignment yes
set_parameter ignore_if_case_statement yes
current_goal cdc/cdc_verify_struct
set_goal_option report {count moresimple moresimple_sevclass sign_off summary waiver CKSGDCInfo Clock-Reset-Summary CDC-report Ac_sync_group_detail Glitch_detailed CrossingInfo SynchInfo Clock-Reset-Detail}
set_parameter dump_sync_info detailed
current_goal cdc/cdc_verify
set_goal_option report {count moresimple moresimple_sevclass sign_off summary waiver CKSGDCInfo Clock-Reset-Summary CDC-report Ac_sync_group_detail Glitch_detailed}
set_parameter fa_atime 20
set_parameter fa_scope block
current_goal dft/dft_scan_ready
set_parameter dftGenerateStuckAtFaultReport all
current_goal dft/dft_best_practice
set_parameter dftGenerateStuckAtFaultReport all
current_goal none
"""

    goals_file.write_text(goals_content)

    print_info(f"File generated at {goals_file}", quiet=quiet)
    print_code(goals_content, "tcl", quiet=quiet)

    # ==========================================================
    # GENERATE WAIVER
    # ==========================================================
    print_step("Generate waiver file", quiet=quiet)

    waiver_content = """## File Name : Local Waiver File(.awl)
waive -file_line {$CVA6_REPO_DIR/common/local/util/sram_cache.sv}  {55}  -severity {  {ERROR}  }  -rule {  {ErrorAnalyzeBBox}  }
waive -file_line {$CVA6_REPO_DIR/common/local/util/sram_cache.sv}  {85}  -severity {  {ERROR}  }  -rule {  {ErrorAnalyzeBBox}  }
waive -file {  {$CVA6_REPO_DIR/vendor/pulp-platform/tech_cells_generic/src/rtl/tc_sram.sv}  }  -severity {  {ERROR}  }  -rule {  {ErrorAnalyzeBBox}  }
waive -file {  {$CVA6_REPO_DIR/vendor/pulp-platform/tech_cells_generic/src/rtl/tc_sram.sv}  }  -severity {  {ERROR}  }  -rule {  {SYNTH_5251}  }
waive -file {  {$CVA6_REPO_DIR/vendor/pulp-platform/tech_cells_generic/src/rtl/tc_sram.sv}  }  -severity {  {SynthesisWarning}  }  -rule {  {SYNTH_5143}  }
waive -file {  {$CVA6_REPO_DIR/core/csr_regfile.sv}  }  -severity {  {SynthesisWarning}  }  -rule {  {SYNTH_89}  }
waive -file {  {$CVA6_REPO_DIR/vendor/pulp-platform/axi/src/axi_pkg.sv} }
waive -file {  {$CVA6_REPO_DIR/core/cva6_rvfi_probes.sv} }
#waive -file {$CVA6_REPO_DIR/core/cache_subsystem/*} -regexp
waive -rule {  {W240}  }  -comment {Remove 'Input declared but not read' warning as it happens very often for disable features such as PMP, Accelerator, ...}
waive -rule {  {W528}  }  -comment {Remove 'Set but not read' warning as it happens very often for disable features such as PMP, Accelerator, ...}
"""

    waiver_file.write_text(waiver_content)

    print_info(f"File generated at {waiver_file}", quiet=quiet)
    print_code(waiver_content, "tcl", quiet=quiet)

    # ==========================================================
    # GENERATE CONSTRAINTS FILE
    # ==========================================================
    print_step("Generate onstraints file", quiet=quiet)

    sgdc_content = f"""## File Name : SpyGlass Constraints File (sgdc file)
current_design {top_elaborate}
clock -name "{top_elaborate}.clk_i" -domain domain0 -tag SG_AUTO_TAG_1 -testclock -atspeed -period 10 -edge {{0 5}}
reset -name "{top_elaborate}.rst_ni" -value 0
test_mode -scanshift -name "{top_elaborate}.rst_ni" -value 1
"""

    sgdc_file.write_text(sgdc_content)

    print_info(f"File generated at {sgdc_file}", quiet=quiet)
    print_code(sgdc_content, "tcl", quiet=quiet)

    # ==========================================================
    # BUILD SPYGLASS DESIGN READ COMMAND
    # ==========================================================

    sg_cmd = ["aipk_read"]
    sg_cmd += [f"-top={top_elaborate}"]
    sg_cmd += [f"-srcfile={str(flist)}"]

    # ==========================================================
    # LAUNCH SPYGLASS DESIGN READ COMMAND
    # ==========================================================
    print_step("LAUNCH SPYGLASS DESIGN READ", quiet=quiet)

    log_file = spyglass_dir / "design_read.log"

    run_cmd(
        cmd=sg_cmd,
        cwd=spyglass_dir,
        env=env_vars,
        error_patterns=["error:|^AIPK_ERROR :|^ERROR:"],
        warning_patterns=["warning:|^AIPK_WARNING :|^WARNING:"],
        highlight_patterns=["info:|Messages:|Total Messages|^AIPK_INFO :|^INFO:"],
        log_file=log_file,
        timeout=1800,
        check=False,
        capture_output=True,
        quiet=quiet,
    )

    # ==========================================================
    # List
    # ==========================================================
    print_step("Generated files", quiet=quiet)
    gen_files = [
        log_file,
        spyglass_dir
        / "sg_run_results"
        / top_elaborate
        / top_elaborate
        / "lint"
        / "design_audit"
        / "spyglass.log",
        spyglass_dir
        / "sg_run_results"
        / top_elaborate
        / top_elaborate
        / "lint"
        / "design_audit"
        / "spyglass_reports",
        spyglass_dir
        / "sg_run_results"
        / top_elaborate
        / top_elaborate
        / "cdc"
        / "cdc_setup_check"
        / "spyglass.log",
        spyglass_dir
        / "sg_run_results"
        / top_elaborate
        / top_elaborate
        / "cdc"
        / "cdc_setup_check"
        / "spyglass_reports",
        spyglass_dir
        / "sg_run_results"
        / f"{top_elaborate}_sg_reports"
        / "html_reports"
        / "goals_summary.html",
    ]

    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}", quiet=quiet)

    # ==========================================================
    # BUILD MANIFEST
    # ==========================================================
    write_manifest(
        spyglass_dir,
        "spyglass-design-read",
        {
            "target": target,
            "testbench_hier": cva6_hier,
            "top_elaborate": top_elaborate,
        },
        quiet=quiet,
    )

    print_recipe_end("Completed", quiet=quiet)
