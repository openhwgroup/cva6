# Verification Plans

This directory contains Verification Plans and plan templates applicable all CORE-V cores.

Refer to the co-locted VerificationPlanning101.md for a description of the philosophy and implementation of CORE-V verification plans.

The subdirectories contain a set of plans for each standard RISCV-V ISA base feature or extension.
The general idea is that all planning regarding frozen RISC-V Unprivileged Specifications should remain in this directory.
Any plans for Privileged Specification, Debug Specification or other core-specific funtionality should reside within plans with the specific core.
Core-specific plans can be found in the core-v-verif/<core>/docs/VerifPlans directory for each core.<br>

|Directory|Description|
|---------|-----------|
|templates| Excel templates for Simulation or Formal verification plans|
|ISA      | Common ISA functionality verification plans|
