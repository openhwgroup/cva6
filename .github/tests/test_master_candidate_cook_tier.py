# Copyright 2026 OpenHW Group
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

from contextlib import contextmanager
import importlib.util
import inspect
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

TEST_CONFIG_DIRECTORY = tempfile.TemporaryDirectory()
unittest.addModuleCleanup(TEST_CONFIG_DIRECTORY.cleanup)
TEST_CONFIG_PATH = Path(TEST_CONFIG_DIRECTORY.name)
(TEST_CONFIG_PATH / "compiler.yml").write_text(
    "test_toolchain:\n"
    "  TOOLS_PATH: /tmp\n"
    "  CLANG: null\n"
    "  GCC: gcc\n"
    "  OBJDUMP: objdump\n"
    "  NM: nm\n"
    "  TARGET_TOOLCHAIN: riscv32-unknown-elf\n",
    encoding="utf-8",
)
(TEST_CONFIG_PATH / "techno.yml").write_text("{}\n", encoding="utf-8")
os.environ["CONFIG_DIR"] = str(TEST_CONFIG_PATH)


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@contextmanager
def working_directory(path: Path):
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


TOOLCHAINS = load_module(
    "prepare_cook_toolchains",
    REPO_ROOT / ".github/scripts/prepare-cook-toolchains.py",
)
RECIPE = load_module(
    "verilator_testharness_run_testlist",
    REPO_ROOT / "flows/recipes/verilator_testharness_run_testlist.py",
)


def load_workflow(name: str) -> dict:
    path = REPO_ROOT / ".github/workflows" / name
    return yaml.load(path.read_text(encoding="utf-8"), Loader=yaml.BaseLoader)


def matrix_entries(workflow: dict, job: str) -> list[dict[str, str]]:
    return workflow["jobs"][job]["strategy"]["matrix"]["include"]


class WorkflowContractTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tier1_path = REPO_ROOT / ".github/workflows/openhw-cva6-ci-tier1.yml"
        self.tier2_path = REPO_ROOT / ".github/workflows/openhw-cva6-ci-tier2.yml"
        self.tier1 = load_workflow(self.tier1_path.name)
        self.tier2 = load_workflow(self.tier2_path.name)
        self.tier1_entries = matrix_entries(self.tier1, "execute-rv32-tier1")
        self.tier2_entries = matrix_entries(self.tier2, "execute-rv32-tier2")

    def test_initial_scope_and_tier_subset(self) -> None:
        tier1_pairs = {
            (entry["config"], entry["testlist"]) for entry in self.tier1_entries
        }
        tier2_pairs = {
            (entry["config"], entry["testlist"]) for entry in self.tier2_entries
        }
        self.assertEqual(
            tier1_pairs,
            {
                ("cv32a60x_axi", "verif/tests/base_rv32_p.yaml"),
                ("cv32a65x_axi", "verif/tests/base_rv32_p.yaml"),
            },
        )
        self.assertEqual(len(tier2_pairs), 5)
        self.assertLessEqual(tier1_pairs, tier2_pairs)

    def test_entries_reference_real_axi_targets_and_testlists(self) -> None:
        for entry in self.tier2_entries:
            target_dir = REPO_ROOT / "config/target" / entry["config"]
            testlist = REPO_ROOT / entry["testlist"]
            self.assertTrue(target_dir.is_dir())
            self.assertTrue(testlist.is_file())
            testbench = yaml.safe_load(
                (target_dir / "testbench_cfg.yml").read_text(encoding="utf-8")
            )
            self.assertEqual(testbench["hier"], "axi")
            tests = yaml.safe_load(testlist.read_text(encoding="utf-8"))["testlist"]
            enabled = [test for test in tests if int(test.get("iterations", 1)) > 0]
            self.assertEqual(len(enabled), int(entry["expected_enabled_tests"]))

    def test_compiler_isa_overrides_follow_rtl_extension_contract(self) -> None:
        expected_zifencei = {
            "cv32a60x_axi": False,
            "cv32a65x_axi": True,
        }
        for entry in self.tier2_entries:
            rtl_config = (
                REPO_ROOT / "config/target" / entry["config"] / "rtl_cfg_pkg.sv"
            ).read_text(encoding="utf-8")
            self.assertIn("RVA: bit'(0)", rtl_config)
            self.assertIn("RVZCMT: bit'(1)", rtl_config)

            zifencei_enabled = expected_zifencei[entry["config"]]
            self.assertIn(
                f"RVZifencei: bit'({int(zifencei_enabled)})",
                rtl_config,
            )
            self.assertEqual(
                "zifencei" in entry["compiler_march"],
                zifencei_enabled,
            )

            if entry["testlist"] == "verif/tests/base_zcmt.yaml":
                self.assertIn("zcmt", entry["compiler_march"])

    def test_workflows_keep_truthful_failure_semantics(self) -> None:
        for path in (self.tier1_path, self.tier2_path):
            text = path.read_text(encoding="utf-8")
            self.assertIn("fail-fast: false", text)
            self.assertIn("if: always()", text)
            self.assertNotIn("continue-on-error", text)
            self.assertNotIn("allow_failure", text)

    def test_no_gitlab_matrix_runtime_dependency(self) -> None:
        paths = (
            self.tier1_path,
            self.tier2_path,
            REPO_ROOT / ".github/scripts/run-tier-regression.sh",
            REPO_ROOT / ".github/actions/setup-cva6-env/action.yml",
        )
        for path in paths:
            self.assertNotIn(".gitlab-ci", path.read_text(encoding="utf-8"))

    def test_master_tier_contract_is_extended_in_place(self) -> None:
        runner = (REPO_ROOT / ".github/scripts/run-tier-regression.sh").read_text(
            encoding="utf-8"
        )
        self.assertIn("cook-testlist", runner)
        self.assertIn('RESULTS_DIR="${RESULTS_DIR:-ci-results}"', runner)
        self.assertIn("${RESULTS_DIR}/run.log", runner)
        self.assertIn("failure_summary.log", runner)
        self.assertIn("exit_code", runner)
        self.assertIn('TIER_ISS_TIMEOUT="${TIER_ISS_TIMEOUT:-500}"', runner)


class RecipeAdapterTest(unittest.TestCase):
    @staticmethod
    def create_compiled_run_fixture(
        root: Path,
        target: str = "cv32a60x_axi",
        tandem_enabled: bool = True,
    ):
        compiled_name = "example_0"
        build_root = root / "build" / target
        compile_dir = build_root / "compile" / compiled_name
        compile_dir.mkdir(parents=True)
        (compile_dir / f"{compiled_name}.elf").write_bytes(b"ELF fixture")
        (compile_dir / "isa_string").write_text(
            "rv32imc_zicsr_zba_zcmt_zifencei\n", encoding="utf-8"
        )
        simulation_root = build_root / "simulation" / "sim_verilator_testharness"
        context = RECIPE.RunContext(
            repo_dir=root,
            target=target,
            target_dir=root / "config" / "target" / target,
            build_root=build_root,
            simulation_root=simulation_root,
            generated_iss_file=build_root / "config" / "cva6.yaml",
            default_mabi="ilp32",
            privilege="msu",
            backend=RECIPE.backend_for(tandem_enabled),
            tandem_enabled=tandem_enabled,
            env={"SPIKE_TANDEM": "1"} if tandem_enabled else {},
            iss_timeout=500,
            sv_seed="7",
            quiet=True,
        )
        return compiled_name, simulation_root, context

    def test_isa_normalization_is_explicit_for_initial_targets(self) -> None:
        cases = {
            "cv32a60x_axi": (
                "rv32imc_zicsr_zba_zcmt",
                "rv32imc_zba_zcmt",
            ),
            "cv32a65x_axi": (
                "rv32imc_zicsr_zba_zcmt_zifencei",
                "rv32imc_zba_zcmt_zifencei",
            ),
        }
        for target, (compiled_isa, expected) in cases.items():
            with self.subTest(target=target):
                self.assertEqual(RECIPE.cva6_input_isa(compiled_isa, target), expected)

    def test_isa_normalization_rejects_unreviewed_target(self) -> None:
        with self.assertRaisesRegex(ValueError, "Unsupported TestHarness target"):
            RECIPE.cva6_input_isa("rv32imac_zicsr_zbkb_zifencei", "cv32a6_imac_sv32")

    def test_isa_normalization_rejects_invalid_isa(self) -> None:
        with self.assertRaisesRegex(ValueError, "Invalid compiled ISA"):
            RECIPE.cva6_input_isa("not-an-isa", "cv32a60x_axi")

    def test_backend_selection_avoids_redundant_standalone_spike(self) -> None:
        self.assertEqual(RECIPE.backend_for(True), "veri-testharness")
        self.assertEqual(RECIPE.backend_for(False), "veri-testharness,spike")

    def test_enabled_tests_rejects_missing_testlist(self) -> None:
        with self.assertRaisesRegex(ValueError, "list named 'testlist'"):
            RECIPE.enabled_tests({}, None)

    def test_enabled_tests_rejects_negative_iterations(self) -> None:
        with self.assertRaisesRegex(ValueError, "Negative iterations"):
            RECIPE.enabled_tests(
                {"testlist": [{"test": "example", "iterations": -1}]}, None
            )

    def test_iss_config_uses_target_spike_yaml(self) -> None:
        source = REPO_ROOT / "verif/sim/cva6.yaml"
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "cva6.yml"
            spike = Path(directory) / "target spike.yml"
            spike.write_text("spike_param_tree: {}\n", encoding="utf-8")
            RECIPE.write_iss_config(source, output, spike)
            data = yaml.safe_load(output.read_text(encoding="utf-8"))
        commands = {
            entry["iss"]: entry["cmd"]
            for entry in data
            if entry["iss"] in {"spike", "veri-testharness"}
        }
        self.assertEqual(len(commands), 2)
        self.assertTrue(all("spike_yaml=" in command for command in commands.values()))

    def test_precompiled_elf_uses_existing_object_interface(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            elf = Path(directory) / "test.elf"
            elf.write_bytes(b"ELF fixture")
            alias = RECIPE.precompiled_object_alias(elf)
            self.assertEqual(alias.suffix, ".o")
            self.assertEqual(alias.read_bytes(), elf.read_bytes())
            self.assertEqual(alias.stat().st_ino, elf.stat().st_ino)

    def test_wrapper_log_survives_cva6_output_cleanup(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            simulation_root = root / "simulation" / "sim_verilator_testharness"
            simulation_dir = simulation_root / "example_0"
            transient_log = simulation_root / "example_0.cook_testharness.log"
            command = [
                sys.executable,
                "-c",
                (
                    "import pathlib, shutil; "
                    f"output = pathlib.Path({str(simulation_dir)!r}); "
                    "shutil.rmtree(output, ignore_errors=True); "
                    "output.mkdir(parents=True); "
                    "print('simulation output')"
                ),
            ]
            return_code = RECIPE.run_streaming(
                command, root, os.environ.copy(), transient_log, quiet=True
            )
            preserved_log = RECIPE.preserve_run_log(transient_log, simulation_dir)

            self.assertEqual(return_code, 0)
            self.assertEqual(preserved_log.read_text(), "simulation output\n")
            self.assertFalse(transient_log.exists())

    def test_regression_report_requires_truthful_success_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "iss_regr.log"

            report.write_text("[PASSED]: 24 matched\n", encoding="utf-8")
            self.assertEqual(
                RECIPE.regression_report_passed(report),
                (True, "24 matched instruction(s) across 1 comparison(s)"),
            )

            report.write_text("[PASSED]: 0 matched\n", encoding="utf-8")
            passed, detail = RECIPE.regression_report_passed(report)
            self.assertFalse(passed)
            self.assertIn("zero-match comparison", detail)

            report.write_text("trace [PASSED]\n", encoding="utf-8")
            passed, detail = RECIPE.regression_report_passed(report)
            self.assertFalse(passed)
            self.assertIn("no pass/fail comparison evidence", detail)

            report.write_text("trace [FAILED]\n", encoding="utf-8")
            passed, detail = RECIPE.regression_report_passed(report)
            self.assertFalse(passed)
            self.assertEqual(detail, "1 failed comparison(s)")

            report.write_text("log without comparison markers\n", encoding="utf-8")
            passed, detail = RECIPE.regression_report_passed(report)
            self.assertFalse(passed)
            self.assertIn("no pass/fail comparison evidence", detail)

            report.unlink()
            passed, detail = RECIPE.regression_report_passed(report)
            self.assertFalse(passed)
            self.assertIn("missing regression report", detail)

    def test_regression_report_rejects_any_zero_match_comparison(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / "iss_regr.log"
            report.write_text(
                "[PASSED]: 24 matched\n[PASSED]: 0 matched\n",
                encoding="utf-8",
            )

            passed, detail = RECIPE.regression_report_passed(report)
            self.assertFalse(passed)
            self.assertIn("zero-match comparison", detail)

    def test_tandem_log_requires_tandem_and_explicit_success(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            simulation_dir = Path(directory)
            log_dir = simulation_dir / "veri-testharness_sim"
            log_dir.mkdir()
            log = log_dir / "test.log.iss"

            passed, detail = RECIPE.tandem_log_passed(simulation_dir)
            self.assertFalse(passed)
            self.assertIn("found 0", detail)

            log.write_text("*** SUCCESS *** (tohost = 0)\n", encoding="utf-8")
            passed, detail = RECIPE.tandem_log_passed(simulation_dir)
            self.assertFalse(passed)
            self.assertIn("missing live Spike tandem evidence", detail)

            log.write_text(
                "Running binary in tandem mode\n"
                "spike_tandem Setting up Spike with binary test.elf\n"
                "*** SUCCESS *** (tohost = 0)\n",
                encoding="utf-8",
            )
            self.assertEqual(
                RECIPE.tandem_log_passed(simulation_dir),
                (True, "TestHarness passed with live Spike tandem"),
            )

            log.write_text(
                "Running binary in tandem mode\n"
                "spike_tandem Setting up Spike with binary test.elf\n"
                "*** SUCCESS *** (tohost = 0)\n"
                "*** FAILED *** (tohost = 1)\n",
                encoding="utf-8",
            )
            passed, detail = RECIPE.tandem_log_passed(simulation_dir)
            self.assertFalse(passed)
            self.assertIn("failure evidence", detail)

    def test_compiled_test_builds_legacy_bridge_command(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = "cv32a60x_axi"
            compiled_name, simulation_root, context = self.create_compiled_run_fixture(
                root, target
            )
            captured: dict[str, object] = {}

            def fake_run(command, cwd, env, log, quiet=False):
                captured.update(command=command, cwd=cwd, env=env, log=log, quiet=quiet)
                log.parent.mkdir(parents=True, exist_ok=True)
                log.write_text("bridge output\n", encoding="utf-8")
                output = Path(command[command.index("--output") + 1])
                testharness_dir = output / "veri-testharness_sim"
                testharness_dir.mkdir(parents=True, exist_ok=True)
                (testharness_dir / "test.log.iss").write_text(
                    "Running binary in tandem mode\n"
                    "spike_tandem Setting up Spike with binary test.elf\n"
                    "*** SUCCESS *** (tohost = 0)\n",
                    encoding="utf-8",
                )
                return 0

            with patch.object(RECIPE, "run_streaming", side_effect=fake_run):
                result = RECIPE.run_compiled_test({"test": "example"}, 0, context)

            command = captured["command"]
            self.assertTrue(result.passed)
            self.assertEqual(result.compiler_isa, "rv32imc_zicsr_zba_zcmt_zifencei")
            self.assertEqual(result.mabi, "ilp32")
            self.assertEqual(
                command[command.index("--isa") + 1], "rv32imc_zba_zcmt_zifencei"
            )
            self.assertEqual(command[command.index("--mabi") + 1], "ilp32")
            self.assertEqual(command[command.index("--iss") + 1], RECIPE.TANDEM_BACKEND)
            self.assertEqual(command[command.index("--iss_timeout") + 1], "500")
            self.assertEqual(command[command.index("--sv_seed") + 1], "7")
            self.assertEqual(captured["env"], {"SPIKE_TANDEM": "1"})
            self.assertEqual(
                (simulation_root / compiled_name / "cook_testharness.log").read_text(
                    encoding="utf-8"
                ),
                "bridge output\n",
            )

    def test_compiled_test_rejects_false_green_child(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, _, context = self.create_compiled_run_fixture(root)

            def fake_run(command, cwd, env, log, quiet=False):
                del cwd, env, quiet
                log.parent.mkdir(parents=True, exist_ok=True)
                log.write_text("0 PASSED, 1 FAILED\n", encoding="utf-8")
                output = Path(command[command.index("--output") + 1])
                testharness_dir = output / "veri-testharness_sim"
                testharness_dir.mkdir(parents=True, exist_ok=True)
                (testharness_dir / "test.log.iss").write_text(
                    "Running binary in tandem mode\n"
                    "spike_tandem Setting up Spike with binary test.elf\n"
                    "*** FAILED *** (tohost = 1)\n",
                    encoding="utf-8",
                )
                return 0

            with patch.object(RECIPE, "run_streaming", side_effect=fake_run):
                result = RECIPE.run_compiled_test({"test": "example"}, 0, context)

            self.assertFalse(result.passed)

    def test_recipe_has_generic_outputs_and_safe_timeout(self) -> None:
        source = (
            REPO_ROOT / "flows/recipes/verilator_testharness_run_testlist.py"
        ).read_text(encoding="utf-8")
        self.assertNotIn("github_actions", source)
        self.assertNotIn("linker_file", source)

        signature = inspect.signature(RECIPE.verilator_testharness_run_testlist)
        timeout_option = signature.parameters["iss_timeout"].default
        tandem_option = signature.parameters["tandem_enabled"].default
        self.assertEqual(timeout_option.default, 500)
        self.assertFalse(tandem_option.default)
        self.assertNotIn("mabi", signature.parameters)

    def test_top_level_command_propagates_failed_test(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = "cv32a60x_axi"
            target_dir = root / "config" / "target" / target
            target_dir.mkdir(parents=True)
            (target_dir / "isa.yml").write_text(
                "mabi: ilp32\n", encoding="utf-8"
            )
            (target_dir / "spike.yaml").write_text(
                "spike_param_tree:\n  priv: MSU\n", encoding="utf-8"
            )

            testlist = root / "verif" / "tests" / "example.yaml"
            testlist.parent.mkdir(parents=True)
            testlist.write_text(
                "testlist:\n  - test: example\n    iterations: 1\n",
                encoding="utf-8",
            )
            source_iss = root / "verif" / "sim" / "cva6.yaml"
            source_iss.parent.mkdir(parents=True)
            source_iss.write_text("{}\n", encoding="utf-8")

            failed_result = RECIPE.CompiledTestResult(
                "example_0", "rv32imc", "ilp32", False
            )
            with (
                working_directory(root),
                patch.object(RECIPE, "write_iss_config"),
                patch.object(
                    RECIPE,
                    "run_compiled_test",
                    return_value=failed_result,
                ),
                patch.object(RECIPE.Report, "dump"),
                self.assertRaises(RECIPE.typer.Exit) as raised,
            ):
                RECIPE.verilator_testharness_run_testlist(
                    target=target,
                    testlist=str(testlist.relative_to(root)),
                    test_name=None,
                    tandem_enabled=True,
                    iss_timeout=500,
                    sv_seed="1",
                    quiet=True,
                )

            self.assertEqual(raised.exception.exit_code, 1)


class ToolchainConfigTest(unittest.TestCase):
    def test_clang_wrapper_forces_lld(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            compiler = Path(directory) / "clang-18"
            compiler.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            compiler.chmod(0o755)
            wrapper = Path(directory) / "clang-riscv32"
            TOOLCHAINS.write_wrapper(wrapper, compiler)
            text = wrapper.read_text(encoding="utf-8")
            self.assertIn("-fuse-ld=lld", text)
            self.assertIn(str(compiler), text)
            self.assertTrue(os.access(wrapper, os.X_OK))

    def test_llvm_probe_failure_only_breaks_required_llvm(self) -> None:
        gcc_config = {"GCC": "riscv32-unknown-elf-gcc"}
        gcc_metadata = {"version": "test-gcc"}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            environment = {
                "RISCV": str(root),
                "CV_SW_PREFIX": "riscv32-unknown-elf-",
            }
            with (
                patch.dict(os.environ, environment),
                patch.object(
                    TOOLCHAINS,
                    "gcc_entry",
                    return_value=(gcc_config, gcc_metadata),
                ),
                patch.object(
                    TOOLCHAINS,
                    "llvm_entry",
                    side_effect=OSError("broken optional LLVM"),
                ),
            ):
                gcc_output = root / "gcc-config"
                with patch.object(
                    sys,
                    "argv",
                    [
                        "prepare-cook-toolchains.py",
                        "--output-dir",
                        str(gcc_output),
                        "--required-toolchain",
                        "github_actions_gcc",
                    ],
                ):
                    TOOLCHAINS.main()

                compiler_data = yaml.safe_load(
                    (gcc_output / "compiler.yml").read_text(encoding="utf-8")
                )
                self.assertEqual(set(compiler_data), {"github_actions_gcc"})

                llvm_output = root / "llvm-config"
                with patch.object(
                    sys,
                    "argv",
                    [
                        "prepare-cook-toolchains.py",
                        "--output-dir",
                        str(llvm_output),
                        "--required-toolchain",
                        "github_actions_llvm18",
                    ],
                ):
                    with self.assertRaisesRegex(
                        SystemExit, "broken optional LLVM"
                    ):
                        TOOLCHAINS.main()


class DependencyContractTest(unittest.TestCase):
    def test_every_cook_requirement_is_constrained(self) -> None:
        requirements = {
            line.strip().lower()
            for line in (REPO_ROOT / "flows/requirements.txt")
            .read_text(encoding="utf-8")
            .splitlines()
            if line.strip() and not line.startswith("#")
        }
        constraints = {
            line.split("==", 1)[0].strip().lower()
            for line in (
                REPO_ROOT / ".github/requirements/cook-tier-ci-constraints.txt"
            )
            .read_text(encoding="utf-8")
            .splitlines()
            if line.strip() and not line.startswith("#")
        }
        self.assertLessEqual(requirements, constraints)


class TraceParserTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        sim_dir = REPO_ROOT / "verif/sim"
        sys.path.insert(0, str(sim_dir))
        sys.path.insert(0, str(sim_dir / "dv/scripts"))
        with working_directory(sim_dir):
            cls.parser = load_module(
                "verilator_log_to_trace_csv",
                sim_dir / "verilator_log_to_trace_csv.py",
            )

    def test_cycle_prefixed_and_legacy_trace_lines_match(self) -> None:
        cycle_line = (
            "        79 | core   0: 0x0000000000010000 "
            "(0x00100413) addi    s0, zero, 1"
        )
        legacy_line = "core   0: 0x0000000000010000 " "(0x00100413) addi    s0, zero, 1"
        self.assertIsNotNone(self.parser.CORE_RE.match(cycle_line))
        self.assertIsNotNone(self.parser.CORE_RE.match(legacy_line))

    def test_cycle_prefixed_trampoline_marker_matches(self) -> None:
        marker = (
            "       105 | core   0: 0x0000000080000000 " "(0x0000a835) DASM(0000a835)"
        )
        self.assertIsNotNone(self.parser.END_TRAMPOLINE_RE.match(marker))


if __name__ == "__main__":
    unittest.main()
