<!--- SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0 --->
This is the root directory of the CV32E40S Verification Plan (aka Test Plan).
Each sub-directory is the verification plan for a specific CV32E40S high-level feature of the same name.

Use the provided CORE-V_Simulation VerifPlan_Template.xlsx spreadsheet as your template to capture a Verification Plan.

## Verification Plan Status

The tables below capture the current status of the Verification Plan for the CV32E40P by high-level feature.  Under the heading `Review` is one of following:
* **Ready for Review**: Vplan has been captured and is awaiting review.
* **Reviewed**: Vplan has been reviewed, and is waiting for updates to address review feedback.
* **Waiting for Signoff**: Vplan has been reviewed and review comments addressed by the author.  Document is now waiting for reviewers to signoff on the post-review updates.
* **Complete**: Post-preview updates have been signed-off.

### Base instruction set plus standard instruction extensions

_Refer to the VerifPlans/ISA/RV32/Simulation directory for specific Verification Plan status for each supported extension._
### Interrupts

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| CLINT   | Incomplete | Incomplete | |

### Debug & Trigger

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| Debug   | Incomplete | Incomplete | |
| Trigger module | Incomplete | Incomplete | |

### Privileged spec

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| CSRs | Incomplete | Incomplete | |
| PMA  | Complete | Ready For Review | |
| User mode | N/A| N/A | Not a CV32E40S Feature |

### Micro-architecure

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| OBI     | Inomplete | Incomplete | |
| Sleep Unit | Incomplete | Incomplete | |
| Pipelines | Incomplete | Incomplete  | |
| Bus errors | Complete | Complete ||
| Bus errors | Complete | Complete | Reviewed and Interated on 8/27/21 |

