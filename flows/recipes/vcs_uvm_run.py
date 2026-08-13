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
import glob
import shutil
import re
import importlib.util
import sys
import random
import typer
from flows.utils.utils import (
    CompMode,
    TraceMode,
    UvmVerbosity,
    autocompletion_target,
    autocompletion_testname_compiled,
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_info,
    print_warning,
    print_success,
    print_error,
    print_param_table,
    tail_file,
    run_cmd,
)


app = typer.Typer()


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def vcs_uvm_run(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    test_name: str = typer.Option(
        ...,
        "--testname",
        "-n",
        help="Test name (compiled from list or not)",
        autocompletion=autocompletion_testname_compiled,
    ),
    comp_mode: CompMode = typer.Option(CompMode.rtl, help="Hardware compilation mode"),
    trace_mode: TraceMode = typer.Option(TraceMode.notrace, help="Trace mode"),
    uvm_verbosity: UvmVerbosity = typer.Option(UvmVerbosity.none, help="UVM verbosity"),
    tandem_enabled: bool = typer.Option(False, help="Enable spike tandem"),
    tb_performance_mode: bool = typer.Option(False, help="Enable tb perf mode"),
    stats: bool = typer.Option(False, help="Enable RTL perf tracer"),
    sim_profile: bool = typer.Option(False, help="Enable simulation profiling"),
    interactive_gui: bool = typer.Option(
        False, help="Launch VERDI for interactive simulation"
    ),
    run_opts: list[str] = typer.Option([], "--run_opts", help="Simulation run options"),
    uvm_seed: str = typer.Option(
        default=str(random.getrandbits(31)), help="Randomize UVM seed"
    ),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    VCS UVM run simulation flow
    """
    # Init code
    code = 0

    # Test tools in path
    vcs_path = shutil.which("vcs")
    if vcs_path is not None:
        print_success(f"VCS: {vcs_path}", quiet=quiet)
    else:
        print_error("vcs: Not found")
        raise typer.Exit(code=1)
    if trace_mode != TraceMode.notrace:
        verdi_path = shutil.which("verdi")
        if verdi_path is not None:
            print_success(f"verdi : {verdi_path}", quiet=quiet)
        else:
            print_error("VERDI: Not found")
            raise typer.Exit(code=1)

    print_recipe_title("VCS DESIGN RUN SIMULATION", quiet=quiet)

    print_param_table(
        {
            "Target": target,
            "Test name": test_name,
            "Compilation mode": comp_mode.value,
            "Trace mode": trace_mode.value,
            "UVM verbosity": uvm_verbosity.value,
            "Tandem enabled": tandem_enabled,
            "TB perf mode": tb_performance_mode,
            "RTL gen perf": stats,
            "Sim profile": sim_profile,
            "Interactive GUI": interactive_gui,
            "Simulation run options": run_opts,
            "UVM seed": uvm_seed,
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

    # Create files and folder paths
    repo_dir = Path.cwd()
    build_root = repo_dir / "build" / target
    compile_dir = build_root / "compile" / test_name
    elab_dir = build_root / "elab" / inout_dir
    simulation_dir = build_root / "simulation" / inout_dir / test_name

    spike_dir = repo_dir / "tools" / "spike"
    spike_dasm = spike_dir / "bin" / "spike-dasm"
    spike_lib = spike_dir / "lib"

    run_do_path = elab_dir / "run.do"
    file_add_tohost = compile_dir / f"{test_name}.add_tohost"
    file_add_GLOBAL_PATTERN_start = (
        compile_dir / f"{test_name}.add_GLOBAL_PATTERN_start"
    )
    file_add_GLOBAL_PATTERN_end = compile_dir / f"{test_name}.add_GLOBAL_PATTERN_end"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean", quiet=quiet)
    try:
        if simulation_dir.exists():
            shutil.rmtree(simulation_dir)
            print_info(f"remove {simulation_dir}", quiet=quiet)
    except Exception as e:
        print_error(f"Clean error : {e}")
        raise typer.Exit(code=1)

    simulation_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {simulation_dir}", quiet=quiet)

    # ==========================================================
    # OPTIONS
    # ==========================================================

    # timing window
    if file_add_tohost.exists():
        add_tohost = file_add_tohost.read_text().strip()
    else:
        print_error(f"Missing {file_add_tohost}")
        raise typer.Exit(code=1)

    if file_add_GLOBAL_PATTERN_start.exists():
        add_start_window = file_add_GLOBAL_PATTERN_start.read_text().strip()
    else:
        print_info(f"Missing {file_add_GLOBAL_PATTERN_start}", quiet=quiet)
        add_start_window = 0

    if file_add_GLOBAL_PATTERN_end.exists():
        add_end_window = file_add_GLOBAL_PATTERN_end.read_text().strip()
    else:
        print_info(f"Missing {file_add_GLOBAL_PATTERN_end}", quiet=quiet)
        add_end_window = 0

    spike_param_file = repo_dir / "config" / "target" / target / "spike.yaml"

    if spike_param_file.exists():
        spike_param_string = f"+config_file={spike_param_file}"
    else:
        spike_param_string = ""
        print_warning("The spike parameter file is missing. Tandem simulation will be configured automatically")

    elf = compile_dir / f"{test_name}.elf"
    signature = compile_dir / f"{test_name}.elf.signature_output"
    tandem_report = simulation_dir / "tandem_report.yml"

    options = [
        f"++{elf}",
        f"+elf_file={elf}",
        f"+core_name={target}",
        "+mhartid=0",
        f"+signature={signature}",
        "+UVM_TESTNAME=uvmt_cva6_firmware_test_c",
        f"+report_file={tandem_report}",
        f"+UVM_VERBOSITY=UVM_{uvm_verbosity}",
        *[f"{run_opt}" for run_opt in run_opts],
        "-assert",
        "nopostproc",
        spike_param_string,
        "-sv_lib",
        f"{spike_lib}/libcustomext",
        "-sv_lib",
        f"{spike_lib}/libyaml-cpp",
        "-sv_lib",
        f"{spike_lib}/libriscv",
        "-sv_lib",
        f"{spike_lib}/libfesvr",
        "-sv_lib",
        f"{spike_lib}/libdisasm",
        "+vcs+lic+wait",
        "-ucli",
        "-do",
        "run.do",
        f"+tandem_enabled={int(tandem_enabled)}",
        f"+tohost_addr={add_tohost}",
        f"+GLOBAL_PATTERN_start={add_start_window}",
        f"+GLOBAL_PATTERN_end={add_end_window}" f"--gui",
    ]

    if interactive_gui:
        options += ["-gui"]
    if sim_profile:
        options += ["-simprofile", "time"]
    if uvm_seed is not None:
        options += [f"+ntb_random_seed={uvm_seed}"]
    if tb_performance_mode:
        options += ["+tb_performance_mode"]
    if comp_mode == CompMode.coverage:
        options += [
            "-cm",
            "line+cond",
            "-cm_name",
            "-cm_seqnoconst",
            "-diag noconst",
            "-cm_cond",
            "arith+for",
            f"{test_name}_{uvm_seed}",
        ]
    if stats:
        options += [
            "+perf_tracer_enabled",
            f"+perf_test_name={test_name}",
            f"+perf_output_dir={simulation_dir}",
        ]

    # ==========================================================
    # RUN.DO GENERATION
    # ==========================================================
    print_step("Generate run.do instructions", quiet=quiet)

    if trace_mode == TraceMode.gui:
        run_do_content = f"""fsdbDumpfile {simulation_dir / "trace.fsdb"}; fsdbDumpvars 0 "uvmt_cva6_tb" +all +trace_process; run"""
    elif trace_mode == TraceMode.fast:
        run_do_content = f"""fsdbDumpfile {simulation_dir / "trace.fsdb"}; fsdbDumpvars 0 "uvmt_cva6_tb" +all +trace_process; run"""
    elif trace_mode == TraceMode.compact:
        run_do_content = f"""dump -file {simulation_dir / "trace.vpd"} -type VPD; dump -add "uvmt_cva6_tb" -depth 0; run"""
    else:
        run_do_content = """run"""

    run_do_path.write_text(run_do_content)
    print_info(f"run.do generated at {run_do_path}", quiet=quiet)
    print_info(f'run.do content: "{run_do_content}"', quiet=quiet)

    # ==========================================================
    # BUILD SIMV COMMAND
    # ==========================================================

    simv_cmd = ["./simv"]
    simv_cmd += options

    # ==========================================================
    # LAUNCH SIMV
    # ==========================================================
    print_step("Run VCS simulation", quiet=quiet)

    log_file = simulation_dir / "simulation.log"

    run_cmd(
        cmd=simv_cmd,
        cwd=elab_dir,
        env=None,
        error_patterns=["(ERROR:|^Error-|^UVM-ERROR|^Fatal-)"],
        warning_patterns=["(WARNING:|^Warning-|^UVM-WARNING)"],
        highlight_patterns=None,
        log_file=log_file,
        timeout=3000,
        check=False,
        capture_output=False,
        quiet=quiet,
    )

    # ==========================================================
    # POST PROCESS LOGS
    # ==========================================================

    # Tail log
    tail_file(log_file, n=20, quiet=quiet)

    status_passed = re.compile(r"^\s+SIMULATION PASSED")
    status_failed = re.compile(r"^\s+SIMULATION FAILED")

    try:
        found = 0
        with log_file.open("r") as f_in:
            for line in f_in:
                if status_passed.search(line):
                    print_success("Simulation PASSED", quiet=quiet)
                    found = 1
                    break
                if status_failed.search(line):
                    print_error("Simulation FAILED")
                    code = 1
                    found = 1
                    break
    except Exception as e:
        print_error(f"Error process log: {e}")

    if found == 0:
        print_error("Simulation status unknown")
        code = 1

    # ==========================================================
    # POST PROCESS TIMING
    # ==========================================================
    print_step("Post-process timing info", quiet=quiet)

    def extract_pattern_to_file(
        log_file, grep_pattern, awk_idx, dest_file, label_begin, label_end
    ):
        try:
            with log_file.open("r") as f_in:
                for line in f_in:
                    if grep_pattern in line:
                        fields = line.split()
                        if len(fields) >= awk_idx + 1:
                            dest_file.write_text(fields[awk_idx])
                            print_success(
                                f"{label_begin} detected at {fields[awk_idx]} {label_end}",
                                quiet=quiet,
                            )
                            break
        except Exception as e:
            print_error(f"Error extraction pattern: {e}")

    # Fallback : windows is 0 to end of simu
    (simulation_dir / "timing_GLOBAL_PATTERN_start").write_text("0")
    (simulation_dir / "timing_GLOBAL_PATTERN_start_cycle").write_text("0")
    extract_pattern_to_file(
        log_file,
        "$finish at simulation time",
        4,
        simulation_dir / "timing_GLOBAL_PATTERN_end",
        "Simulation end time",
        "ns",
    )
    extract_pattern_to_file(
        log_file,
        "*** [rvfi_tracer] INFO: Simulation terminated after",
        6,
        simulation_dir / "timing_GLOBAL_PATTERN_end_cycle",
        "Simulation end cycle",
        "cycles",
    )
    # Window is the between GLOBAL_PATTERN symbol only
    extract_pattern_to_file(
        log_file,
        "*** [rvfi_tracer] INFO: GLOBAL_PATTERN_start",
        7,
        simulation_dir / "timing_GLOBAL_PATTERN_start",
        "Symbol GLOBAL_PATTERN_start",
        "ns",
    )
    extract_pattern_to_file(
        log_file,
        "*** [rvfi_tracer] INFO: GLOBAL_PATTERN_end",
        7,
        simulation_dir / "timing_GLOBAL_PATTERN_end",
        "Symbol GLOBAL_PATTERN_end",
        "ns",
    )
    extract_pattern_to_file(
        log_file,
        "*** [rvfi_tracer] INFO: GLOBAL_PATTERN_start",
        9,
        simulation_dir / "timing_GLOBAL_PATTERN_start_cycle",
        "Symbol GLOBAL_PATTERN_start",
        "cycles",
    )
    extract_pattern_to_file(
        log_file,
        "*** [rvfi_tracer] INFO: GLOBAL_PATTERN_end",
        9,
        simulation_dir / "timing_GLOBAL_PATTERN_end_cycle",
        "Symbol GLOBAL_PATTERN_end",
        "cycles",
    )

    # ==========================================================
    # Disassemble rvfi trace with spike_dasm
    # ==========================================================
    print_step("Disassemble rvfi trace", quiet=quiet)

    spike_dasm_log_file = simulation_dir / "spike_dasm.log"
    isa = (compile_dir / "isa_string").read_text()

    trace_rvfi_file = elab_dir / "trace_rvfi_hart_00.dasm"

    if trace_rvfi_file.exists():
        print_step("Disassemble rvfi trace", quiet=quiet)

        env_vars = {"LD_LIBRARY_PATH": f"{spike_lib}"}

        spike_dasm_cmd = [str(spike_dasm)]
        spike_dasm_cmd += [f"--isa={isa}"]

        with trace_rvfi_file.open("rb") as f:
            run_cmd(
                cmd=spike_dasm_cmd,
                cwd=elab_dir,
                env=env_vars,
                error_patterns=["(ERROR|Error|No such file or directory)"],
                warning_patterns=["(WARNING|Warning)"],
                highlight_patterns=None,
                stdin=f,
                log_file=spike_dasm_log_file,
                timeout=30,
                check=False,
                capture_output=False,
                quiet=quiet,
            )
    else:
        print_info(
            "Trace RVFI not found, if rvfi interface is disabled it's normal",
            quiet=quiet,
        )

    # ==========================================================
    # MOVE LOGS / TRACES
    # ==========================================================
    print_step("Move files", quiet=quiet)

    for pattern in [
        elab_dir / "tandem.log",
        elab_dir / "trace_rvfi_hart*.dasm",
    ]:
        for file_path in glob.glob(str(pattern)):
            try:
                shutil.move(file_path, str(simulation_dir))
                print_info(f"Moved {file_path} -> {simulation_dir}", quiet=quiet)
            except FileNotFoundError:
                print_error(f"No file matched: {file_path}")
            except Exception as e:
                print_error(f"Failed to move {file_path}: {e}")

    # ==========================================================
    # Stats
    # ==========================================================
    if stats:
        print_step("Analysis Stats", quiet=quiet)

        path_script = (
            repo_dir / "perf-model" / "rtl_models_trace" / "scripts" / "main_stats.py"
        )
        path_json = simulation_dir / f"stalls_{test_name}_{target}.json"

        directory_script = str(path_script.parent)
        sys.path.insert(0, directory_script)

        try:
            spec = importlib.util.spec_from_file_location("main_stats", path_script)
            main_stats = importlib.util.module_from_spec(spec)
            sys.modules["main_stats"] = main_stats
            spec.loader.exec_module(main_stats)
            try:
                main_stats.main(
                    files=[str(path_json)], csv=True, i=None, pc=None, c=None, v=None
                )
            except SystemExit as e:
                pass

        finally:
            if directory_script in sys.path:
                sys.path.remove(directory_script)

    # ==========================================================
    # List
    # ==========================================================

    gen_files = [
        simulation_dir / "simulation.log",
        simulation_dir / "tandem.log",
        simulation_dir / "trace_rvfi_hart_00.dasm",
        simulation_dir / "spike_dasm.log",
        simulation_dir / "timing_GLOBAL_PATTERN_start",
        simulation_dir / "timing_GLOBAL_PATTERN_end",
        simulation_dir / "trace.fsdb",
        simulation_dir / "trace.vpd",
        simulation_dir / f"stalls_{test_name}_{target}.json",
        simulation_dir / f"details_{test_name}_{target}.txt",
        simulation_dir / f"analysis_{test_name}_{target}.txt",
    ]

    print_step("Generated files", quiet=quiet)
    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}", quiet=quiet)

    print_recipe_end("Completed", quiet=quiet)

    if code != 0:
        raise typer.Exit(code=1)
