## Functional verification of CSRs in a RISC-V core
The Controll and Status Registers in a RISC-V core are distinct from CSRs in
non-processor ASIC/FPGA RTL in ways that have a direct impact on RTL
verification.  Here, we discuss the problem in detail, using select RISC-V
standard CSRs as examples.

This document serves two purposes.  The first purpose is a general discussion
and tutorial on the topic of CSR verification in general and RISC-V CSR
verification in particular.   Its second purpose is form the Verification Plan
(also known as a Testplan) for the CV32E40P CSRs.   Note that this Vplan does
not follow the same spreadsheet style template that is used for other CV32E40P
Vplans.   The reason for this will become apparent as you read the document.

### Power-on-Reset Values

Many (all?) RISC-V CSRs are expected to have a known value once the core comes
out of hardware reset.  Testing these values is typically straightforward and
is done in a way that is familiar to anyone who has done this for non-processor
ASIC/FPGA RTL.  In both cases, care must be taken to read the value of a status
register before the device-under-test experiences an event that causes an update
to the register.  For example, accessing a non-existant CSR should raise an
illegal instruction exception which should, in turn, update the value of MCAUSE.
Therefore a test that checks the PoR value of MCAUSE must not access a non-existant
CSR before reading MCAUSE.

### Access Mode Behavior

Here, we are trying to answer the question, "how does the CSR behave when it is
accessed (written to, or read from)?".  In RISC-V cores, CSRs are accessed using
the `CSRRC`, `CSRRCI`, `CSRRS`, `CSRRSI`, `CSRRW` and `CSRRWI` instructions.  Note
that there are also seven pseudoinstructions that will expand into one of these
instructions.  While in the general case a core may provide alternative means to
access CSRs, in the CV32E40P, these instructions are the only access method available.

Note that when verifying access mode behavior we are not (yet) concerned about
what the core will do when a given CSR has a specific value.

In RISC-V cores, access mode behavior has four dimensions: access mode,
privilege, existance and field specification.  These are discussed in turn,
with emphasis placed on pre-silicon functional verification (as opposed to 
post-silicon use by software).

#### Access Mode

Access modes in RISC-V cores are simple and familar to those with prior experience
with non-processor core ASIC/FPGA RTL.  In fact, there are only two access modes
to worry about: RW and RO:

1. RW: all bits of a RW field must be writable and must return the last written
value upon a read.
2. RO: no bit of a RO field may be writable and must return the previous value upon
read, event after being written to by either 0 or 1.

#### Privilege

Of course, nothing is ever _that_ simple with RISC-V.  A core's privilege mode adds
a second dimension to access mode.  Is it often the case that a CSR that is
accessible in a high privilege mode does not exist in lower modes. This must also
be verified.

For the purposes of CSR verification, it is permissible to consider Debug Mode as
the highest privilege level.

CV32E40P only supports Machine mode, which greatly simplifies the problem.

#### Existance

CSR "existance" is a concept unique to processor core and is not generally seen in
non-processor ASIC/FPGA RTL designs.  The RISC-V privileged and debug specifications
define a set of CSRs, including both "required" and "optional" CSRs.  Accessing an
optional CSR may result in an illegal instruction (which must be veified).  A
complicating factor is that CSR existance may also be dependent on privlege level.
For example reading a Debug CSR when the core is not in debug mode results in an
illegal instruction exception while reading the same register in debug mode
returns a value.

#### Field Specification

Although the "field specification" may sound familiar to those with a
non-processor RTL background, the term is used differently in RISC-V where
"field specification" refers to how software is expected to interact with
specific fields of specific CSRs.  This has a material impact on the strategy
used for RTL verification of CSRs.  There are three field specification types:

1. **WPRI**: this field specification defines how software should interact
with specific "protected" fields.  This software action is wholly independent of RTL
logic behavior, so WPRI fields may be treated as RO for the purposes of RTL
functional verification of their access behavior.
2. **WLRL**: once again, this field specification refers to how software should
interact with specific RW fields.  The difference is that reads will only return
_legal_ values on reads, acting as a mask on return values of a RW test.  In all
other respects, WLRL fields may be treated as RW for the purposes of RTL
functional verification of their access behavior.
3. **WARL**: fields may be treated as RW (with read masking) for the purposes of RTL functional
verification of their access behavior.


### Control Actions

CSRs are called Control and Status Registers for a reason.  Control registers will
change (control) the operation of the device under test in measureable ways and functional
verification must coverage all legal values (or in some cases, important ranges of
values) and then check that these values have the desired affect.  A good example
is ensuring that interrupts are asserted when MSTATUS[MIE] is both 0/1 and ensuring
that interrupts are ignored or responded to, as appropriate.

Control register verification of RISC-V cores is not conceptually different than 
control register verification of non-processor ASIC/FPGA RTL.  One difference is
that in non-processor RTL, the control path (reading the writing the CSRs) is
typically independent of the data path (events that are affected by control
register values).  In processor cores a program executing on the core acts as both
the control path (by executing CSR access instructions) and the data path (by
executing code that is affected by the CSRs).

### Status Capture

Certain external and/or program events will be recorded in status registers.
This sub-section will be updated at a later date.

## CV32E40P CSR Verification Plan

| Testcase | Targeted Aspect | Type | Reference | Status |
|----------|-----------------|------|-----------|--------|
| por\_csr.c | Power-on-Reset values | Manually written, directed | [1](#1) | Complete |
| por\_debug\_csr.c | Power-on-Reset values for Debug CSRs | Manually written, directed | [2](#2) | |
| csr\_existance.c | Illegal instruction exception for non-existant CSRs | Manually written, directed | [3](#3) | |
| cv32e40p_csr\_access_test.c | Combined access mode behavior and field specification tests for all CSRs | Generated | [4](#4) | Under development |
| csr\_privlege.c | Debug mode can access all CSRs | Manually written, directed | [5](#5) | |

### ToDo:

* Verification of status fields.
* Verification of control fields.

### 1
At the time of this writting (2020-10-07), this is implemented as two tests, `modeled_csr_por` and `requested_csr_por`.  In the near (?) future these will be combined into a single test.  For each machine-mode CSR in CV32E40P:
- read current value
- compare to documented PoR value in User Manual

Failure conditions:
- any read value does not match documented PoR
- any illegal instruction exceptions

### 2
Same as [1](#1) but first enter debug mode and then attempt to read all
machine-mode and debug-mode registers

### 3
Similar to [1](#1) with added accesses between address ranges of existing
machine-mode CSRs.  For example, address range 0x307 : 0x33F between Machine
Trap Setup CSRs and Machine Trap Handling CSRs.

### 4
Access mode test of all CSRs.  This is a generated test based on [cv32e40p_csr_template.yaml](https://github.com/openhwgroup/core-v-verif/blob/master/vendor_lib/google/corev-dv/cv32e40p_csr_template.yaml).

### 5
Same as [4](#4), run in Debug mode.  Add access mode testing of Debug CSRs.
