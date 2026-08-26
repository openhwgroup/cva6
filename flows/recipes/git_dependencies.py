# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

# Please refer to flows/README.md to add target

import os
import shutil
from pathlib import Path

import typer
import yaml

from flows.utils.utils import (
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_info,
    print_success,
    print_error,
    print_warning,
    run_cmd,
)

app = typer.Typer()


# ==========================================================
# RECIPE - Git dependencies
# ==========================================================


@app.command()
def git_dependencies(
    repo: list[str] = typer.Option(
        [],
        "--repo",
        "-r",
        help="Specific dependency to install (e.g., 'riscv-tests', 'riscv-compliance'). If empty, install all.",
    ),
    force: bool = typer.Option(
        False, "--force", "-f", help="Force re-clone even if directory exists"
    ),
    quiet: bool = typer.Option(False, "--quiet", "-q", help="Suppress output"),
):
    """
    Install external Git dependencies for CVA6 verification.

    This recipe clones external test repositories (riscv-tests, riscv-compliance, riscv-arch-test)
    as defined in flows/config/dependencies.yml. These are NOT Git submodules.

    Examples:
        # Install all external dependencies
        ./cook.py git-dependencies

        # Install specific dependency
        ./cook.py git-dependencies --repo riscv-tests

        # Force re-install (re-clone even if exists)
        ./cook.py git-dependencies --repo riscv-tests --force

        # Install multiple dependencies
        ./cook.py git-dependencies --repo riscv-tests --repo riscv-compliance
    """

    # Title
    print_recipe_title("Git Dependencies", quiet=quiet)

    # ==========================================================
    # Load dependencies configuration
    # ==========================================================
    print_step("Loading dependencies configuration", quiet=quiet)

    repo_dir = Path.cwd()
    config_dir = Path(os.getenv("CONFIG_DIR", repo_dir / "flows" / "config"))
    config_file = config_dir / "dependencies.yml"
    if not config_file.exists():
        print_error(f"Configuration file not found: {config_file}", quiet=quiet)
        print_recipe_end("Failed", quiet=quiet)
        raise typer.Exit(code=1)

    try:
        with config_file.open("r") as f:
            dependencies = yaml.safe_load(f)
    except yaml.YAMLError as e:
        print_error(f"Failed to parse YAML configuration: {e}", quiet=quiet)
        print_recipe_end("Failed", quiet=quiet)
        raise typer.Exit(code=1)

    if not dependencies:
        print_error("No dependencies found in configuration file", quiet=quiet)
        print_recipe_end("Failed", quiet=quiet)
        raise typer.Exit(code=1)

    print_success(f"Loaded {len(dependencies)} dependency definitions", quiet=quiet)
    # ==========================================================
    # Select dependencies to install
    # ==========================================================
    if repo:
        # Install specific dependencies
        deps_to_install = {}
        for dep_name in repo:
            if dep_name not in dependencies:
                print_error(f"Unknown dependency: {dep_name}", quiet=quiet)
                print_error(
                    f"Available dependencies: {', '.join(dependencies.keys())}",
                    quiet=quiet,
                )
                print_recipe_end("Failed", quiet=quiet)
                raise typer.Exit(code=1)
            deps_to_install[dep_name] = dependencies[dep_name]
        print_info(
            f"Installing {len(deps_to_install)} specific dependency(ies): {', '.join(deps_to_install.keys())}",
            quiet=quiet,
        )
    else:
        # Install all dependencies
        deps_to_install = dependencies
        print_info(f"Installing all {len(deps_to_install)} dependencies", quiet=quiet)

    # ==========================================================
    # Install each dependency
    # ==========================================================
    all_success = True

    for dep_name, dep_config in deps_to_install.items():
        print_step(f"Processing dependency: {dep_name}", quiet=quiet)
        # Validate dependency configuration
        if not isinstance(dep_config, dict):
            print_error(
                f"Invalid configuration for {dep_name}: expected dict, got {type(dep_config)}",
                quiet=quiet,
            )
            all_success = False
            continue

        repo_url = dep_config.get("repo")
        branch = dep_config.get("branch", "main")
        commit = dep_config.get("commit")
        destination = dep_config.get("destination")
        patches = dep_config.get("patches", [])
        submodules = dep_config.get("submodules", False)
        post_install = dep_config.get("post_install", {})

        # Validate required fields
        if not repo_url:
            print_error(f"Missing 'repo' field for dependency: {dep_name}", quiet=quiet)
            all_success = False
            continue

        if not destination:
            print_error(
                f"Missing 'destination' field for dependency: {dep_name}", quiet=quiet
            )
            all_success = False
            continue

        dest_path = repo_dir / destination
        # Check if destination exists
        if dest_path.exists():
            if force:
                print_warning(
                    f"Destination exists, forcing re-clone: {dest_path}", quiet=quiet
                )
                try:
                    shutil.rmtree(dest_path)
                    print_info(f"Removed existing directory: {dest_path}", quiet=quiet)
                except Exception as e:
                    print_error(
                        f"Failed to remove directory {dest_path}: {e}", quiet=quiet
                    )
                    all_success = False
                    continue
            else:
                print_warning(
                    f"Destination already exists, skipping: {dest_path}", quiet=quiet
                )
                print_info("Use --force to re-clone", quiet=quiet)
                continue

        # Create parent directories if needed
        dest_path.parent.mkdir(parents=True, exist_ok=True)

        # Clone repository
        print_info(f"Cloning {repo_url} to {destination}", quiet=quiet)
        clone_cmd = ["git", "clone", "--branch", branch, repo_url, str(dest_path)]

        try:
            result = run_cmd(
                cmd=clone_cmd,
                cwd=repo_dir,
                env=None,
                error_patterns=None,
                warning_patterns=None,
                highlight_patterns=None,
                log_file=None,
                timeout=300,  # 5 minutes timeout
                check=False,
                capture_output=True,
                quiet=quiet,
            )

            if (
                result is None
                or "fatal:" in result.lower()
                or "error:" in result.lower()
            ):
                print_error(f"Failed to clone {dep_name}", quiet=quiet)
                all_success = False
                continue

            print_success(f"Successfully cloned {dep_name}", quiet=quiet)
        except Exception as e:
            print_error(f"Exception during clone: {e}", quiet=quiet)
            all_success = False
            continue

        # Checkout specific commit if specified
        if commit:
            print_info(f"Checking out commit: {commit}", quiet=quiet)
            checkout_cmd = ["git", "checkout", commit]

            try:
                result = run_cmd(
                    cmd=checkout_cmd,
                    cwd=dest_path,
                    env=None,
                    error_patterns=None,
                    warning_patterns=None,
                    highlight_patterns=None,
                    log_file=None,
                    timeout=60,
                    check=False,
                    capture_output=True,
                    quiet=quiet,
                )

                if (
                    result is None
                    or "fatal:" in result.lower()
                    or "error:" in result.lower()
                ):
                    print_error(f"Failed to checkout commit {commit}", quiet=quiet)
                    all_success = False
                    continue

                print_success(f"Checked out commit: {commit}", quiet=quiet)
            except Exception as e:
                print_error(f"Exception during checkout: {e}", quiet=quiet)
                all_success = False
                continue

        # Initialize submodules if needed
        if submodules:
            print_info("Initializing submodules recursively", quiet=quiet)
            submodule_cmd = ["git", "submodule", "update", "--init", "--recursive"]

            try:
                result = run_cmd(
                    cmd=submodule_cmd,
                    cwd=dest_path,
                    env=None,
                    error_patterns=None,
                    warning_patterns=None,
                    highlight_patterns=None,
                    log_file=None,
                    timeout=300,
                    check=False,
                    capture_output=True,
                    quiet=quiet,
                )

                if (
                    result is None
                    or "fatal:" in result.lower()
                    or "error:" in result.lower()
                ):
                    print_warning(
                        f"Failed to initialize submodules for {dep_name}", quiet=quiet
                    )
                else:
                    print_success("Submodules initialized", quiet=quiet)
            except Exception as e:
                print_warning(
                    f"Exception during submodule initialization: {e}", quiet=quiet
                )

        # Apply patches if any
        if patches:
            print_info(f"Applying {len(patches)} patch(es)", quiet=quiet)

            for patch_spec in patches:
                # Parse patch specification
                # Format: "path/to/patch.patch" or "path/to/patch.patch:subdirectory"
                if ":" in patch_spec:
                    patch_file_rel, patch_subdir = patch_spec.split(":", 1)
                    patch_cwd = dest_path / patch_subdir
                else:
                    patch_file_rel = patch_spec
                    patch_cwd = dest_path

                patch_file = repo_dir / patch_file_rel
                if not patch_file.exists():
                    print_error(f"Patch file not found: {patch_file}", quiet=quiet)
                    all_success = False
                    continue

                if not patch_cwd.exists():
                    print_error(
                        f"Patch subdirectory not found: {patch_cwd}", quiet=quiet
                    )
                    all_success = False
                    continue

                print_info(
                    f"Applying patch: {patch_file.name} in {patch_cwd.relative_to(repo_dir)}",
                    quiet=quiet,
                )

                # Apply patch using git apply
                patch_cmd = ["git", "apply", str(patch_file)]
                try:
                    result = run_cmd(
                        cmd=patch_cmd,
                        cwd=patch_cwd,
                        env=None,
                        error_patterns=None,
                        warning_patterns=None,
                        highlight_patterns=None,
                        log_file=None,
                        timeout=60,
                        check=False,
                        capture_output=True,
                        quiet=quiet,
                    )

                    if (
                        result is None
                        or "fatal:" in result.lower()
                        or "error:" in result.lower()
                    ):
                        print_error(
                            f"Failed to apply patch: {patch_file.name}", quiet=quiet
                        )
                        all_success = False
                        continue

                    print_success(f"Applied patch: {patch_file.name}", quiet=quiet)
                except Exception as e:
                    print_error(f"Exception during patch apply: {e}", quiet=quiet)
                    all_success = False
                    continue

        # Handle post-install steps
        if post_install:
            print_info("Running post-install steps", quiet=quiet)

            # Special handling for Spike target copy (riscv-arch-test)
            if post_install.get("copy_spike_target", False):
                print_info("Copying Spike target definitions", quiet=quiet)

                # Get SPIKE_PATH from environment (defined in setenv.sh)
                spike_path = os.getenv("SPIKE_PATH")
                if not spike_path:
                    print_warning(
                        f"SPIKE_PATH not set - cannot copy arch_test_target for {dep_name}. "
                        "Please set SPIKE_PATH in flows/config/setenv.sh and source it.",
                        quiet=quiet,
                    )
                else:
                    # SPIKE_SRC_DIR = SPIKE_PATH/riscv-isa-sim
                    spike_target_src = (
                        Path(spike_path) / "riscv-isa-sim" / "arch_test_target"
                    )
                    spike_target_dst = dest_path / "riscv-target"

                    if spike_target_src.exists():
                        print_info(
                            f"Copying Spike arch_test_target from {spike_target_src} to {spike_target_dst}",
                            quiet=quiet,
                        )

                        try:
                            # Remove existing destination if it exists
                            if spike_target_dst.exists():
                                shutil.rmtree(spike_target_dst)

                            # Copy the directory
                            shutil.copytree(spike_target_src, spike_target_dst)

                            print_success(
                                "Successfully copied Spike arch_test_target",
                                quiet=quiet,
                            )
                        except Exception as e:
                            print_error(
                                f"Failed to copy Spike target: {e}", quiet=quiet
                            )
                            all_success = False
                    else:
                        print_warning(
                            f"Spike arch_test_target not found at {spike_target_src}. "
                            f"Expected: $SPIKE_PATH/riscv-isa-sim/arch_test_target. "
                            "Please ensure Spike is installed correctly.",
                            quiet=quiet,
                        )

        print_success(f"Completed installation of {dep_name}", quiet=quiet)
    # ==========================================================
    # Final summary
    # ==========================================================
    if all_success:
        print_recipe_end("Completed successfully", quiet=quiet)
    else:
        print_recipe_end("Completed with errors", quiet=quiet)
        raise typer.Exit(code=1)
