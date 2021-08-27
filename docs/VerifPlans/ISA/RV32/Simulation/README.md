<!--- SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0 --->
This is the simulation testplan directory for the RV32 ISA I architecture and the supported extensions in CORE-V cores.

Use the provided CORE-V_Simulation VerifPlan_Template.xlsx spreadsheet as your template to capture a Verification Plan.

## Verification Plan Status

*Update: 8/2/21 The Vplans are being updates to take advantage of new features offered by the ISACOV UVM Agent.  These updates
will be rolled into the coverage models for the cv32e40x and cv32e40s first but eventually will be integrated into all RV32 CoreV testbenches*

The tables below capture the current status of the Verification Plan for RV32 ISA by ISA extension.  Under the heading `Review` is one of following:
* **Not Captured**: Vplan has not been captured.
* **Ready for Review**: Vplan has been captured and is awaiting review.
* **Reviewed**: Vplan has been reviewed, and is waiting for updates to address review feedback.
* **Waiting for Signoff**: Vplan has been reviewed and review comments addressed by the author.  Document is now waiting for reviewers to signoff on the post-review updates.
* **Complete**: Post-preview updates have been signed-off.

### Base instruction set plus standard instruction extensions

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| RV32I | Complete | Complete | Reviewed and integrated on 7/30/21 |
| M extension | Complete | Complete | Reviewed and integrated on 7/30/21 |
| C extension | Complete | Complete | Reviewed and integrated on 8/27/21 |
| A extension | Complete | Complete | Reviewed and integrated on 8/27/21 |
| Zifencei extension | Complete | Complete | Reviewed and integrated on 8/27/21 |
| Zicsr extension | Complete | Complete | Reviewed and integrated on 8/27/21 |
| B extension (Zba,Zbb,Zbc,Zbs) | Complete | Complete | Reviewed and integrated on 8/27/21 |
| Zce extension | In progress | Not Captured | |
| Counter extension | In progress | Not Captured | |
| Instruction Exceptions | In progress | Not Captured |  |
| Sequential Instructions | Complete | Complete | Reviewed and integrated on 8/27/21 |