#!/usr/bin/env python3
# Copyright 2026 OpenHW Group
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Create reproducible cook.py compiler entries for public GitHub runners."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import shutil
import stat
import subprocess
from typing import Any

import yaml


def require_executable(path: Path) -> Path:
    if not path.is_file() or not os.access(path, os.X_OK):
        raise ValueError(f"Missing executable tool: {path}")
    return path.resolve()


def find_executable(*names: str) -> Path:
    for name in names:
        found = shutil.which(name)
        if found:
            return require_executable(Path(found))
    raise ValueError(f"Cannot find executable: {', '.join(names)}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def first_version_line(path: Path) -> str:
    result = subprocess.run(
        [str(path), "--version"],
        check=True,
        capture_output=True,
        text=True,
    )
    return (result.stdout or result.stderr).splitlines()[0]


def write_wrapper(path: Path, compiler: Path) -> None:
    path.write_text(
        "#!/usr/bin/env bash\n" f'exec "{compiler}" -fuse-ld=lld "$@"\n',
        encoding="utf-8",
    )
    path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


def link_tool(destination: Path, source: Path) -> None:
    if destination.exists() or destination.is_symlink():
        destination.unlink()
    destination.symlink_to(source)


def gcc_entry(riscv: Path, prefix: str) -> tuple[dict[str, Any], dict[str, Any]]:
    bin_dir = riscv / "bin"
    tools = {
        "GCC": f"{prefix}gcc",
        "OBJDUMP": f"{prefix}objdump",
        "NM": f"{prefix}nm",
    }
    paths = {name: require_executable(bin_dir / tool) for name, tool in tools.items()}
    entry = {
        "TOOLS_PATH": str(riscv),
        "CLANG": None,
        **tools,
        "TARGET_TOOLCHAIN": prefix.rstrip("-"),
    }
    metadata = {
        "version": first_version_line(paths["GCC"]),
        "target_toolchain": prefix.rstrip("-"),
        "binaries": {
            name.lower(): {"path": str(path), "sha256": sha256(path)}
            for name, path in paths.items()
        },
    }
    return entry, metadata


def llvm_entry(output_dir: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    clang = find_executable("clang-18")
    objdump = find_executable("llvm-objdump-18", "llvm-objdump")
    nm = find_executable("llvm-nm-18", "llvm-nm")
    lld = find_executable("ld.lld-18", "ld.lld")

    tool_root = output_dir / "llvm18"
    bin_dir = tool_root / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    write_wrapper(bin_dir / "clang-riscv32", clang)
    link_tool(bin_dir / "llvm-objdump", objdump)
    link_tool(bin_dir / "llvm-nm", nm)
    link_tool(bin_dir / "ld.lld", lld)

    entry = {
        "TOOLS_PATH": str(tool_root),
        "CLANG": "clang-riscv32",
        "GCC": None,
        "OBJDUMP": "llvm-objdump",
        "NM": "llvm-nm",
        "TARGET_TOOLCHAIN": "riscv32-unknown-elf",
    }
    metadata = {
        "version": first_version_line(clang),
        "target_toolchain": "riscv32-unknown-elf",
        "linker": str(lld),
        "binaries": {
            "clang": {"path": str(clang), "sha256": sha256(clang)},
            "objdump": {"path": str(objdump), "sha256": sha256(objdump)},
            "nm": {"path": str(nm), "sha256": sha256(nm)},
            "lld": {"path": str(lld), "sha256": sha256(lld)},
        },
    }
    return entry, metadata


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument(
        "--required-toolchain",
        choices=("github_actions_gcc", "github_actions_llvm18"),
        required=True,
    )
    args = parser.parse_args()

    try:
        riscv = Path(os.environ["RISCV"]).resolve()
        prefix = os.environ["CV_SW_PREFIX"]
        output_dir = args.output_dir.resolve()
        output_dir.mkdir(parents=True, exist_ok=True)

        compiler_data: dict[str, Any] = {}
        environment: dict[str, Any] = {
            "schema_version": 1,
            "required_toolchain": args.required_toolchain,
            "toolchains": {},
        }
        gcc, gcc_metadata = gcc_entry(riscv, prefix)
        compiler_data["github_actions_gcc"] = gcc
        environment["toolchains"]["github_actions_gcc"] = gcc_metadata

        try:
            llvm, llvm_metadata = llvm_entry(output_dir)
            compiler_data["github_actions_llvm18"] = llvm
            environment["toolchains"]["github_actions_llvm18"] = llvm_metadata
        except ValueError:
            if args.required_toolchain == "github_actions_llvm18":
                raise

        if args.required_toolchain not in compiler_data:
            raise ValueError(f"Toolchain is unavailable: {args.required_toolchain}")

        (output_dir / "compiler.yml").write_text(
            yaml.safe_dump(compiler_data, sort_keys=False), encoding="utf-8"
        )
        (output_dir / "techno.yml").write_text("{}\n", encoding="utf-8")
        (output_dir / "environment.yml").write_text(
            yaml.safe_dump(environment, sort_keys=False), encoding="utf-8"
        )
        print(f"Prepared {args.required_toolchain} in {output_dir}")
        print(environment["toolchains"][args.required_toolchain]["version"])
    except (KeyError, OSError, ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"ERROR: {error}") from error


if __name__ == "__main__":
    main()
