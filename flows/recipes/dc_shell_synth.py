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
from enum import Enum
import re
from functools import reduce
import yaml
import typer
from flows.utils.config_loader import load_techno_config
from flows.utils.manifest import write_manifest
from flows.utils.utils import (
    Cva6Hier,
    TechnoOption,
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


class PreProcOption(str, Enum):
    HPDCACHE_ASSERT_OFF = "HPDCACHE_ASSERT_OFF"
    RVFI_ENABLE = "RVFI_ENABLE"


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def dc_shell_synth(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    techno: TechnoOption = typer.Option(
        ..., help="Techno defined in $CONFIG_DIR/techno.yml"
    ),
    period: str = typer.Option(..., help="Synthesis target period"),
    script_file: str = typer.Option("dc.tcl", help="dc setup script"),
    preprocessor_defines: list[PreProcOption] = typer.Option(
        [PreProcOption.HPDCACHE_ASSERT_OFF], "--define", help="Preprocessor directives"
    ),
    clean: bool = typer.Option(True, help="Clean working dir before"),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    DC Shell Synthesis flow
    """
    define_one_string = (
        "{ " + reduce(lambda a, b: f"{a}, {b}", preprocessor_defines) + " }"
    )

    print_recipe_title("Dc shell synthesis flow", quiet=quiet)

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
            "Techno": techno.value,
            "Period": period,
            "Script": script_file,
            "Preprocessor defines": define_one_string,
            "Clean": clean,
        },
        "Options",
        quiet=quiet,
    )

    # Get config
    #
    TECHNO_DATA = load_techno_config()
    techno = TECHNO_DATA[techno.value]

    print_param_table(
        techno,
        "Techno parameters",
        quiet=quiet,
    )

    # Test tools in path
    dc_shell_path = shutil.which("dc_shell")
    if dc_shell_path is not None:
        print_success(f"dc_shell: {dc_shell_path}", quiet=quiet)
    else:
        print_error("dc_shell: Not found", quiet=quiet)
        raise typer.Exit(code=1)

    # Create files and folder paths
    synth_dir = repo_dir / "build" / target / "synthesis"
    rm_flow = repo_dir / "RM_FLOW" / "synth"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean", quiet=quiet)
    if clean:
        try:
            if synth_dir.exists():
                shutil.rmtree(synth_dir)
                print_info(f"remove {synth_dir}", quiet=quiet)
        except Exception as e:
            print_error(f"Clean error : {e}", quiet=quiet)
            raise typer.Exit(code=1)
    else:
        print_info(f"Skip cleaning {synth_dir}", quiet=quiet)

    synth_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {synth_dir}", quiet=quiet)

    # print config in synth_dir
    with open(synth_dir / "build_config.yaml", "w", encoding="utf-8") as f:
        yaml.dump(techno, f, default_flow_style=False)
        print("Generated file : ", synth_dir / "build_config.yaml")

    # ==========================================================
    # CUSTOMIZE WITH OPTIONS
    # ==========================================================

    # SDF HIERARCHY (Gate only)
    if cva6_hier == Cva6Hier.obi:
        top_elaborate = "cva6_example_obi"
    elif cva6_hier == Cva6Hier.axi:
        top_elaborate = "cva6_example_axi"
    else:
        print_error("Unknown cva6_hier", quiet=quiet)
        raise typer.Exit(code=1)

    # ==========================================================
    # ENV VARIABLES (passed to run_cmd only)
    # ==========================================================

    env_vars = {
        "TOP": "cva6_top",
        "TOP_ELABORATE": top_elaborate,
        "TOP_SYNTHESIS": "cva6_top__*",
        "TARGET": target,
        "TARGET_CFG": target,
        "CVA6_REPO_DIR": str(repo_dir),
        "HPDCACHE_DIR": str(repo_dir / "core/cache_subsystem/hpdcache"),
        "HPDCACHE_TARGET_CFG": str(repo_dir / "/core/include/cva6_hpdcache_"),
        "PERIOD": period,
        "TOP_LIB": "ariane_lib",
        "IP_LIST": "",
        "DC_FILE": "",
        "LIST_FF": "ON",
        "LIST_CKG": "OFF",
        "FF_DETAILS": "OFF",
        "FAST_SYNTH": "OFF",
        "TERM": "vt100",
        "SCRIPTS_DIR": "",
        "SNPSLMD_QUEUE": "TRUE",
    }

    env_vars |= techno

    # ==========================================================
    # GENERATE FLIST FOR DC_SHELL
    # ==========================================================
    print_step("Generate Flist.cva6_synth", quiet=quiet)

    def parse_flist(flist_path, patterns, collected=None):

        if collected is None:
            collected = []

        flist_path = Path(flist_path)
        if not flist_path.exists():
            raise FileNotFoundError(f"Flist not found: {flist_path}")

        with flist_path.open("r", encoding="utf-8") as f:
            text = f.read()
            # Expand environement variables to be able to follow include Flist
            for search, replace in patterns:
                text = text.replace(search, replace)
            lines = text.splitlines()

        for line in lines:
            l = line.strip()
            # Skip empty/comments/+incdir
            if not l or l.startswith("//") or l.startswith("+incdir+"):
                continue

            # Recursive include -F
            if l.startswith("-F"):
                flist_incl = l[2:].strip()
                parse_flist(flist_incl, patterns, collected)
                continue

            collected.append(
                f"analyze -f sverilog -lib ariane_lib -define {define_one_string} {l}\n"
            )

        return collected

    flist_envvar = [
        ("${TARGET_CFG}", target),
        ("${CVA6_REPO_DIR}", str(repo_dir)),
        ("${HPDCACHE_DIR}", str(repo_dir / "core/cache_subsystem/hpdcache")),
    ]

    analyse_files = parse_flist(
        repo_dir / "config" / "target" / target / "Flist.cva6", flist_envvar
    )

    # Write Flist.cva6_synth in rm_flow dir
    (rm_flow / "Flist.cva6_synth").write_text("".join(analyse_files))

    # ==========================================================
    # CUSTOMIZE WITH OPTIONS
    # ==========================================================

    options = [
        "-no_gui",
        "-no_log",
        "-topographical_mode",
        "-f",
        f"{rm_flow / 'rm_dc_scripts' / script_file}",
    ]

    # ==========================================================
    # BUILD DC_SHELL COMMAND
    # ==========================================================

    dc_cmd = ["dc_shell"]
    dc_cmd += options

    # ==========================================================
    # LAUNCH DC_SHELL COMMAND
    # ==========================================================
    print_step("Launch dc_shell", quiet=quiet)

    log_file = synth_dir / "synthesis.log"

    run_cmd(
        cmd=dc_cmd,
        cwd=rm_flow,
        env=env_vars,
        error_patterns=["^Error:|^RM-Error"],
        warning_patterns=None,
        highlight_patterns=["^RM-Info"],
        log_file=log_file,
        timeout=6000,
        check=False,
        capture_output=False,
        quiet=quiet,
    )

    # ==========================================================
    # Post-process netlist/sdf/spef
    # ==========================================================
    print_step("Post-process netlist/reports", quiet=quiet)

    top = env_vars["TOP"]
    TARGET = env_vars["TARGET"]
    TECH_NAME = env_vars["TECH_NAME"]
    SCENARIO_SYNTH = techno["SCENARIO_SYNTH_NAME"]
    SCENARIO_POWER = env_vars["SCENARIO_POWER_NAME"]

    files_to_post_process = [
        # (src, dest)
        (
            synth_dir / "netlist" / f"{top}_{TARGET}_{TECH_NAME}_synth.v",
            synth_dir / "netlist" / "synth.v",
        ),
        (
            synth_dir
            / "netlist"
            / f"{top}_{TARGET}_{TECH_NAME}_synth.{SCENARIO_SYNTH}.sdf",
            synth_dir / "netlist" / "wc_timing.sdf",
        ),
        (
            synth_dir
            / "netlist"
            / f"{top}_{TARGET}_{TECH_NAME}_synth.{SCENARIO_POWER}.sdf",
            synth_dir / "netlist" / "wc_power.sdf",
        ),
        (
            synth_dir
            / "netlist"
            / f"{top}_{TARGET}_{TECH_NAME}_synth.{SCENARIO_POWER}.spef",
            synth_dir / "netlist" / "wc_power.spef",
        ),
        (
            synth_dir / "reports" / f"{top}_{TARGET}_{TECH_NAME}_synth_area.rpt",
            synth_dir / "reports" / "synth_area.rpt",
        ),
    ]

    for src, dst in files_to_post_process:
        if src.exists():
            # sed "s/${TOP}__[0-9]\+/${TOP}/g"
            with src.open("r") as f_in, dst.open("w") as f_out:
                for line in f_in:
                    f_out.write(re.sub(rf"{top}__\d+", top, line))

        else:
            print_error(f"{src} missing", quiet=quiet)

    # Write Flist.libverilog to help compile step
    (synth_dir / "Flist.libverilog").write_text(env_vars["LIB_VERILOG"])

    # ==========================================================
    # BUILD MANIFEST
    # ==========================================================
    write_manifest(
        synth_dir,
        "dc-shell-synth",
        {
            "target": target,
            "techno": techno.get("TECH_NAME", None),
            "period": period,
            "script_file": script_file,
            "preprocessor_defines": preprocessor_defines,
        },
        quiet=quiet,
    )

    # ==========================================================
    # Reporting area
    # ==========================================================
    print_step("Area reporting", quiet=quiet)

    NAND2_AREA = int(env_vars["NAND2_AREA"])

    pattern_global_val = re.compile(
        r"^(Combinational area|Buf/Inv area|Noncombinational area|Macro/Black Box area):\ *(\d*\.\d*)$",
        re.MULTILINE,
    )
    pattern_hier = re.compile(
        r"^(\w*(?:\/\w*){0,2})\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\w*)$",
        re.MULTILINE,
    )

    try:
        with (synth_dir / "reports" / "synth_area.rpt").open("r") as f:
            log = f.read()
            global_val = pattern_global_val.findall(log)
            hier = pattern_hier.findall(log)
    except Exception as e:
        print_error(f"Error process log: {e}", quiet=quiet)

    total_area = float(hier[0][1])
    kgates = total_area / NAND2_AREA

    result_metric = {"Total area": f"{kgates:.2f} kgates ({total_area:.2f})"}
    for i in global_val:
        rel_area = 0 if total_area == 0 else int(float(i[1]) / total_area * 100)
        result_metric |= {i[0]: f"{rel_area} %"}

    print_param_table(
        result_metric,
        "Global results",
        quiet=quiet,
    )

    result_metric = {}
    for i in hier:
        result_metric |= {
            i[0]: f"{float(i[1]) / NAND2_AREA:.2f} kGates - {float(i[2]):.2f} %"
        }

    print_param_table(
        result_metric,
        "Hierarchies details",
        quiet=quiet,
    )

    # ==========================================================
    # List
    # ==========================================================
    print_step("Generated files", quiet=quiet)
    gen_files = [
        log_file,
        synth_dir / "warnings.log",
        synth_dir / "errors.log",
        synth_dir / "Flist.libverilog",
        synth_dir / "reports" / "synth_area.rpt",
        synth_dir / "netlist" / "synth.v",
        synth_dir / "netlist" / "wc_timing.sdf",
        synth_dir / "netlist" / "wc_power.sdf",
        synth_dir / "netlist" / "wc_power.spef",
    ]
    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}", quiet=quiet)

    print_recipe_end("Completed", quiet=quiet)
