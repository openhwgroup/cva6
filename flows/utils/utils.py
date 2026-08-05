# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

# Please refer to flows/README.md to add target

import subprocess
import os
import re
import signal
import platform
from enum import Enum
from pathlib import Path
import typer
from rich.console import Console
from rich.panel import Panel
from rich.rule import Rule
from rich.padding import Padding
from rich.table import Table
from rich.syntax import Syntax
from rich.text import Text
import yaml
from flows.utils.config_loader import load_techno_config, load_compiler_config


# ==========================================================
# Print functions
# ==========================================================

console = Console()

TECHNO_DATA = load_techno_config(verbose = False)
COMPILER_DATA = load_compiler_config(verbose = False)

def print_recipe_title(title, quiet=False):
    if not quiet:
        console.print(
            Panel(
                title,
                expand=True,
                style="bold",
                border_style="blue",
            )
        )


def print_recipe_end(msg, quiet=False):
    if not quiet:
        console.print(msg, style="bold cyan")


def print_step(msg, quiet=False):
    if not quiet:
        console.print(Rule(msg, style="bold cyan"))


def print_info(msg, end="\n", highlight=False, quiet=False):
    if not quiet:
        console.print(f"{msg}", style="white", end=end, highlight=highlight)


def print_success(msg, end="\n", highlight=False, quiet=False):
    if not quiet:
        # pylint: disable-next=anomalous-backslash-in-string
        console.print(f"\[{msg}]", style="green", end=end, highlight=highlight)


def print_error(msg, end="\n", highlight=False, quiet=False):
    if not quiet:
        console.print(f"{msg}", style="red", end=end, highlight=highlight)


def print_warning(msg, end="\n", highlight=False, quiet=False):
    if not quiet:
        console.print(f"{msg}", style="yellow", end=end, highlight=highlight)


def print_cmd(msg, end="\n", highlight=False, quiet=False):
    if not quiet:
        console.print(f"[CMD] {msg}", style="cyan", end=end, highlight=highlight)


def print_param_table(params, title, quiet=False):
    if not quiet:
        table = Table(show_header=False, box=None)
        table.add_column("Name")
        table.add_column("Value")
        if isinstance(params, dict):
            for n, v in params.items():
                table.add_row(n, str(v))
            console.print(
                Panel(
                    table,
                    title=title,
                    title_align="left",
                    border_style="white",
                    expand=False,
                )
            )


def print_table(params, title, column_name, style, quiet=False):
    if not quiet:
        table = Table(show_header=False, box=None)
        for i, name in enumerate(column_name):
            table.add_column(name, style=style[i])
        table.add_row(*column_name)
        for k, v in params.items():
            table.add_row(k, *v)

        console.print(
            Panel(
                table,
                title=title,
                title_align="left",
                border_style="white",
                expand=False,
            )
        )


def print_code(file, lang, quiet=False):
    if not quiet:
        console.print(Padding(Syntax(file, lang, word_wrap=True), (0, 2)))


def tail_file(file_path, n=20, quiet=False):
    if not quiet:
        try:
            with file_path.open("r") as f:
                lines = f.readlines()
            last_lines = lines[-n:] if len(lines) >= n else lines
            for line in last_lines:
                print(line, end="")
        except Exception as e:
            print_error(f"Error tail: {e}")


def print_file_regex(
    file_path,
    error_patterns=None,
    warning_patterns=None,
    highlight_patterns=None,
    quiet=False,
):
    if not quiet:
        err = [re.compile(p, re.I) for p in (error_patterns or [])]
        warn = [re.compile(p, re.I) for p in (warning_patterns or [])]
        high = [re.compile(p, re.I) for p in (highlight_patterns or [])]
        try:
            with file_path.open("r") as f:
                lines = f.readlines()
            for line in lines:
                if any(p.search(line) for p in err):
                    console.print(Text(line), style="bold white on red", end="")
                elif any(p.search(line) for p in warn):
                    console.print(Text(line), style="black on yellow", end="")
                elif any(p.search(line) for p in high):
                    console.print(Text(line), end="")
        except Exception as e:
            print_error(f"Error print results: {e}")


# ==========================================================
# Command runner
# ==========================================================


def run_cmd(
    cmd,
    *,
    cwd=None,
    env=None,
    error_patterns=None,
    warning_patterns=None,
    highlight_patterns=None,
    stdin=None,
    log_file=None,
    timeout=None,
    check=True,
    capture_output=True,
    quiet=False,
):
    """
    Robust command runner
    """

    if isinstance(cmd, str):
        print_error(
            "Error: Cmd is a string, Passing a command as a string is not supported. Prefer a list of arguments to avoid shell parsing issues"
        )

    err = [re.compile(p, re.I) for p in (error_patterns or [])]
    warn = [re.compile(p, re.I) for p in (warning_patterns or [])]
    high = [re.compile(p, re.I) for p in (highlight_patterns or [])]

    full_env = {**os.environ, **(env or {})}

    popen_kwargs = {
        "stdout": subprocess.PIPE,
        "stderr": subprocess.STDOUT,
        "stdin": stdin,
        "text": True,
        "bufsize": 1,
        "env": full_env,
        "cwd": cwd,
        "shell": False,
        "close_fds": True,
    }

    if platform.system() == "Windows":
        popen_kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        popen_kwargs["start_new_session"] = True

    print_info("Set current working directory:", quiet=quiet)
    print_code(str(cwd), "bash", quiet=quiet)

    print_info("Command launched:", quiet=quiet)
    if isinstance(cmd, list):
        print_code(" ".join(cmd), "bash", quiet=quiet)
    else:
        print_code(cmd, "bash", quiet=quiet)

    print_param_table(env, "Environment variables", quiet=quiet)

    if stdin is None:
        print_info("Stdin: Not used", quiet=quiet)
    else:
        print_info("Stdin: Used", quiet=quiet)

    process = subprocess.Popen(cmd, **popen_kwargs)

    logfile = log_file.open("w") if log_file else None
    collected_output = []
    print_info("[Begin]", quiet=quiet)
    try:
        for line in iter(process.stdout.readline, ""):

            if capture_output:
                collected_output.append(line)

            if logfile:
                logfile.write(line)
                logfile.flush()

            if not quiet:
                if any(p.search(line) for p in err):
                    console.print(Text(line), style="bold white on red", end="")
                elif any(p.search(line) for p in warn):
                    console.print(Text(line), style="black on yellow", end="")
                elif any(p.search(line) for p in high):
                    console.print(Text(line), style="black on green", end="")

        process.stdout.close()
        process.wait(timeout=timeout)

    except KeyboardInterrupt:
        print_warning("\nInterrupted! Killing process group...")

        if platform.system() == "Windows":
            # pylint: disable-next=no-member
            process.send_signal(signal.CTRL_BREAK_EVENT)
        else:
            pgid = os.getpgid(process.pid)
            os.killpg(pgid, signal.SIGTERM)
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(pgid, signal.SIGKILL)
        raise

    finally:
        if logfile:
            logfile.close()
        print_info("[End]", quiet=quiet)

    if check and process.returncode != 0:
        raise RuntimeError(f"Command failed ({process.returncode})")

    if capture_output:
        return "".join(collected_output)

    return None


# ==========================================================
# AUTOCOMPLETION
# ==========================================================


class CompMode(str, Enum):
    rtl = "rtl"
    gate_wc_power = "gate_wc_power"
    gate_wc_timing = "gate_wc_timing"
    coverage = "coverage"


class TraceMode(str, Enum):
    gui = "gui"
    fast = "fast"
    compact = "compact"
    notrace = "notrace"


class UvmVerbosity(str, Enum):
    none = "NONE"
    low = "LOW"
    medium = "MEDIUM"
    high = "HIGH"
    full = "FULL"
    debug = "DEBUG"


class Cva6Hier(str, Enum):
    obi = "obi"
    axi = "axi"

if TECHNO_DATA != None:
    TechnoOption = Enum("TechnoOption", {key.upper(): key for key in TECHNO_DATA.keys()})
else:
    TechnoOption = Enum("TechnoOption", [])

if COMPILER_DATA != None:
    ToolchainOption = Enum(
        "ToolchainOption", {key.upper(): key for key in COMPILER_DATA.keys()}
    )
else:
    ToolchainOption = Enum("ToolchainOption", [])

def autocompletion_target():
    target_list = []
    target_path = Path.cwd() / "config" / "target"
    if not target_path.exists():
        return target_list
    for elmt in target_path.iterdir():
        if elmt.is_dir():
            target_list += [elmt.name]
    return target_list


def autocompletion_testname_compiled(ctx: typer.Context):
    testname_list = []
    target = ctx.params["target"]
    target_build_path = Path.cwd() / "build" / target / "compile"
    if not (target and target_build_path.exists()):
        print("Missing target or any compiled test found")
        return testname_list
    for d in target_build_path.iterdir():
        if d.is_dir():
            testname_list += [d.name]
    return testname_list


def autocompletion_testlist(ctx: typer.Context):
    testlist_list = []
    testlist_path_list = [Path.cwd() / "verif" / "tests"]
    target = ctx.params["target"]
    if target:
        testlist_path_list += [Path.cwd() / "config" / "target" / target / "verif"]
    for path in testlist_path_list:
        if path.exists():
            for file in path.iterdir():
                if file.is_file() and (
                    file.name.endswith(".yaml") or file.name.endswith(".yml")
                ):
                    testlist_list += [str(file.relative_to(Path.cwd()))]
    return testlist_list


def autocompletion_testname_in_testlist(ctx: typer.Context):
    testname_list = []
    testlist = ctx.params["testlist"]
    if testlist:
        testlist_path = Path.cwd() / testlist
    else:
        print("Missing testlist")
        return testname_list
    if not testlist_path.exists():
        print(f"Missing {testlist_path}")
        return testname_list
    with testlist_path.open("r") as f:
        data = yaml.safe_load(f)
    for v in data["testlist"]:
        testname_list += [v["test"]]
    return testname_list


def autocompletion_param_config(ctx: typer.Context):
    param_list = []
    target = ctx.params["target"]
    target_cfg = Path.cwd() / "core" / "include" / f"{target}_config_pkg.sv"
    if not (target and target_cfg.exists()):
        print(f"Missing core/include/{target}_config_pkg.sv")
        return param_list
    pattern = re.compile(r"^\s*(\w*)\s*:.*$")
    with (target_cfg).open("r") as f:
        for line in f:
            match = pattern.search(line)
            if match:
                param_list += [match.group(1).strip()]
    return param_list
