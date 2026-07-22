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
from flows.utils.config_loader import COMPILER_DATA
from flows.utils.utils import (
    ToolchainOption,
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
def sw_compile(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    toolchain: ToolchainOption = typer.Option(
        ..., "--toolchain", "-c", help="Toolchain defined in $CONFIG_DIR/compiler.yml"
    ),
    src_files: list[str] = typer.Argument(..., help="Source files"),
    inc_dirs: list[str] = typer.Option([], "--inc", help="Include directories"),
    linker_file: str = typer.Option(..., "--linker", help="Linker file path"),
    options: list[str] = typer.Option([], "--options", help="Options"),
    march: str = typer.Option(
        None, help="march custom instead of default one from config/target"
    ),
    mabi: str = typer.Option(
        None, help="mabi custom instead of default one from config/target"
    ),
    preprocessor_directives: list[str] = typer.Option(
        [], "--define", help="Preprocessor directives"
    ),
    test_name: str = typer.Option(
        ..., "--out", help="Test name (used in rest of flow)"
    ),
):
    """
    Compile software and generate ELF + reports.
    """
    print_recipe_title("Software compilation")

    print_param_table(
        {
            "Target": target,
            "Toolchain": toolchain,
            "Sources": src_files,
            "Includes": inc_dirs,
            "Linker": linker_file,
            "options": options,
            "march": march,
            "mabi": mabi,
            "Defines": preprocessor_directives,
            "test_name": test_name,
        },
        "Options",
    )

    repo_dir = Path.cwd()

    # Get config
    compiler_data = COMPILER_DATA[toolchain.value]

    print_param_table(
        compiler_data,
        "Compiler parameters",
    )

    if compiler_data["CLANG"] is not None:
        print_info("LLVM mode")
        compiler = compiler_data["CLANG"]
    else:
        print_info("GCC mode")
        compiler = compiler_data["GCC"]

    tools_path = compiler_data["TOOLS_PATH"]
    objdump = compiler_data["OBJDUMP"]
    nm = compiler_data["NM"]
    target_toolchain = compiler_data["TARGET_TOOLCHAIN"]

    # Create files and folder paths
    build_root = repo_dir / "build" / target
    compile_dir = build_root / "compile" / test_name
    elf_file = compile_dir / f"{test_name}.elf"
    objdump_file = compile_dir / f"{test_name}.dump"
    size_file = compile_dir / f"{test_name}.size"
    add_tohost_file = compile_dir / f"{test_name}.add_tohost"
    add_GLOBAL_PATTERN_start_file = (
        compile_dir / f"{test_name}.add_GLOBAL_PATTERN_start"
    )
    add_GLOBAL_PATTERN_end_file = compile_dir / f"{test_name}.add_GLOBAL_PATTERN_end"
    isa_config_file = repo_dir / "config" / "target" / target / "isa.yml"
    isa_string_file = compile_dir / "isa_string"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean")
    try:
        if compile_dir.exists():
            shutil.rmtree(compile_dir)
            print_info(f"remove {compile_dir}")
    except Exception as e:
        print_error(f"Clean error : {e}")
        raise typer.Exit(code=1)

    compile_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {compile_dir}")

    # ==========================================================
    # ISA STRING SELECTION
    # ==========================================================

    print_step("ISA string selection")

    if mabi is None or march is None:
        # If not provided (standard case), take ISA string in target config directory
        if isa_config_file.exists():
            with isa_config_file.open("r", encoding="utf-8") as f:
                isa_config = yaml.safe_load(f)

            try:
                if mabi is None:
                    mabi = isa_config["mabi"]
                if march is None:
                    march = isa_config["march"]
            except KeyError as e:
                print_error(
                    f"Error: Keys '{mabi}' or '{march}' missing in {isa_config_file}"
                )
                raise typer.Exit(code=1) from e
        else:
            print_error(f"Missing {isa_config_file}")
            raise typer.Exit(code=1)

    if linker_file is None:
        linker_file = str(repo_dir / "config" / "target" / target / "link.ld")

    print_param_table(
        {
            "mabi": mabi,
            "march": march,
            "linker_file": linker_file,
        },
        "ISA and Linker file",
    )

    # ==========================================================
    # LAUNCH COMPILER COMMAND
    # ==========================================================
    print_step("Compilation")

    compile_cmd = [
        f"{tools_path}/bin/{compiler}",
        *src_files,
        *[f"-I{inc}" for inc in inc_dirs],
        f"-T{linker_file}",
        *[f"-{option}" for option in options],
        f"-march={march}",
        f"-mabi={mabi}",
        *[f"-D{macro}" for macro in preprocessor_directives],
        "-o",
        str(elf_file),
    ]
    if compiler_data["CLANG"] is not None:
        compile_cmd += [
            f"--target={target_toolchain}",
        ]

    run_cmd(
        cmd=compile_cmd,
        cwd=None,
        env=None,
        error_patterns=["error"],
        warning_patterns=["warning"],
        highlight_patterns=None,
        log_file=compile_dir / "compile.log",
        timeout=90,
        check=False,
        capture_output=False,
    )

    if elf_file.exists():
        print_success("Compilation successful")
    else:
        print_error("Compilation failed")
        raise typer.Exit(code=1)

    isa_string_file.write_text(march)

    # ==========================================================
    # Objdump
    # ==========================================================
    print_step("Objdump")

    compile_cmd = [f"{tools_path}/bin/{objdump}", "-D", str(elf_file)]

    run_cmd(
        cmd=compile_cmd,
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=None,
        log_file=objdump_file,
        timeout=90,
        check=False,
        capture_output=False,
    )

    if objdump_file.exists():
        print_success("Objdump generated")
    else:
        print_error("Objdump failed")
        raise typer.Exit(code=1)

    # ==========================================================
    # Section size report
    # ==========================================================
    print_step("Sections size reporting")

    compile_cmd = ["size", "-A", str(elf_file)]

    run_cmd(
        cmd=compile_cmd,
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=None,
        log_file=size_file,
        timeout=90,
        check=False,
        capture_output=False,
    )

    if size_file.exists():
        print_success("Size report generated")
    else:
        print_error("Size report failed")
        raise typer.Exit(code=1)

    # ==========================================================
    # Symbols extraction
    # ==========================================================
    print_step("Symbols extraction")

    def extract_symbol(symbol_name: str, output_file: Path):

        compile_cmd = [f"{tools_path}/bin/{nm}", str(elf_file)]

        result = run_cmd(
            cmd=compile_cmd,
            cwd=None,
            env=None,
            error_patterns=None,
            warning_patterns=None,
            highlight_patterns=None,
            log_file=None,
            timeout=90,
            check=False,
            capture_output=True,
        )

        for line in result.splitlines():
            parts = line.split()
            if len(parts) >= 3 and parts[2] == symbol_name:
                addr = parts[0]
                output_path = output_file
                output_path.write_text(addr)
                if output_file.exists():
                    print_success(f"{symbol_name}: {addr}")
                else:
                    print_error(f"Write file failed; {symbol_name}: {addr}")
                return

        print_error(f"{symbol_name} not found")
        return

    extract_symbol("tohost", add_tohost_file)
    extract_symbol("GLOBAL_PATTERN_start", add_GLOBAL_PATTERN_start_file)
    extract_symbol("GLOBAL_PATTERN_end", add_GLOBAL_PATTERN_end_file)

    # ==========================================================
    # List
    # ==========================================================
    print_step("Generated files")
    gen_files = [
        add_tohost_file,
        objdump_file,
        size_file,
        add_tohost_file,
        add_GLOBAL_PATTERN_start_file,
        add_GLOBAL_PATTERN_end_file,
        isa_string_file,
    ]
    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}")

    print_recipe_end("Completed")
