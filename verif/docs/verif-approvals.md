# Approvals of CVA6 verification tasks
For each verification task on CVA6 v5.0.0, the artefacts have to be checked.
It means dedicated approvals for each artifact produced by engineers.

## Approval
To approve an artefact, the approving person has to update this document.

## User manual chapter/section
For some the topics, the user manual chapter may only describe differences
and precisions with existing specifications
like RISC-V Instruction Set Manual, AXI Protocol, or CV-X-IF.
For other ones (when no specification already exists), it shall be a brand new chapter.

Each chapter/section has to be formally approved.

## DV plan (VP tool)
Based on the user manual, DV plan is written using the VP tool which
provides a way to have text files allowing easier differences than binary format.

Each DV plan has to be formally approved.

## Test bench
To implement the DV plan, the test bench has to be enriched.
When needed a UVM agent has to be developed or to be reused from core-v-verif.
Such UVM agents have to be generic as much as possible to be reusable.
Specific CVA6 behaviours have to be part of the CVA6 UVM environment.

To exercise the DUT, tests have to be added. Two types of tests are possible:
- Generated ones: produced by riscv-dv
- Directed ones: hand crafted to address specific cases difficult to exercise with generated tests

The implementation of the different components (tests, code coverage, assertions, agents,...) have to be formally approved.

## Coverage
- Functional coverage: if not 100%, missing points explained and approved
- Code coverage: provide delta results after new tests
- Results available in CI dashboard

The results of coverage and the missing points have to be formally approved.

## GitHub issues
Once running tests, discrepancies with the expected behaviour can be observed.
For each of them, a GitHub issue has to be created with the relevant
information (e.g. a detailed explanation how to reproduce the problem).

Each issue has to be assigned.


## ISACOV

| Task            | Date       | Owner                 | Approved by           | Commit hash  | link to extra information (GitHub issue, doc,..) |
| --------------- | ---------- | --------------------- | --------------------- | ------------ | ------------------------------------------------ |
| User Manual     | 2023-05-26 | Ayoub Jalali          | André Sintzoff        | [be58d57d](https://github.com/openhwgroup/cva6/commit/be58d57d)| [User Manual chapter](https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/RISCV_Instructions.html) |
| DV plan         | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Test bench      | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Coverage        | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Assigned Issues | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |

## CV-X-IF

| Task            | Date       | Owner                 | Approved by           | Commit hash  | link to extra information (GitHub issue, doc,..) |
| --------------- | ---------- | --------------------- | --------------------- | ------------ | ------------------------------------------------ |
| User Manual     | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| DV plan         | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Test bench      | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Coverage        | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Assigned Issues | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |

## AXI

| Task            | Date       | Owner                 | Approved by           | Commit hash  | link to extra information (GitHub issue, doc,..) |
| --------------- | ---------- | --------------------- | --------------------- | ------------ | ------------------------------------------------ |
| User Manual     | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| DV plan         | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Test bench      | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Coverage        | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
| Assigned Issues | YYYY-MM-DD | First name, Last name | First name, Last name | 8 characters | 50 characters                                    |
