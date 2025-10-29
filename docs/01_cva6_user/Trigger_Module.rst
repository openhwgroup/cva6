..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales DIS SAS

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


Trigger Module (Sdtrig Extension)
=================================
The module provides powerful hardware breakpoints and watchpoints in the core. 
Upon trigger match, the core supports two actions i.e. breakpoint excpetion generation and entry into debug mode.
The number of triggers is parameterized and the module itself is configurable under the SDTRIG bit.

Configuration CSRs
~~~~~~~~~~~~~~~~~~
* ``tselect``  : The currently selected trigger.
* ``tinfo``    : Shows the currently supported triggers.
* ``tdata1``   : Specifies trigger data like trigger type, configuration, privilege mode, status.
* ``tdata2``   : The value to be matched.
* ``tdata3``   : Specifies context data.
* ``scontext`` : Specifies supervisor mode context data.


Modified CSRs (Breakpoint action)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* ``mstatus``: several fields are updated like previous privilege mode (``MPP``), previous interrupt enabled (``MPIE``)
* ``mepc``   : updated with the address of the instruction raising the exception.
* ``mcause`` : updated with a breakpoint code (0x00000003) indicating the event causing the trap.

Modified CSRs (Debug action)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* ``dpc``    : updated with the address of the instruction causing the debug request.
* ``dcsr``   : some fields are updated like debug entry cause (``CAUSE``)


Icount
------
The ``icount`` trigger is used to delay a breakpoint or debug entry by a programmable number of instructions. It acts like a countdown timer based on instruction commits and gives deterministic trigger behavior useful for testing or stepping into debug mode after a specific number of instructions.

Prerequisites
~~~~~~~~~~~~~
- ``SDTRIG`` and ``Icount`` configuration bits must be enabled.
- Trigger type must be ``4'd3`` in ``tdata1``.

Trigger Match Logic
~~~~~~~~~~~~~~~~~~~
- The ``count`` field in ``tdata1`` is initialized with the number of instructions to wait.
- The counter decrements on every instruction commit (``commit_ack_i``).
- Countdown continues only outside trap handlers (``!in_trap_handler``) to avoid miscounts during exceptions.

- Matching occurs when:
  - ``count == 0``
  - Current privilege level matches the trigger config (``m/s/u``)

- On match:
  - ``pending`` is set
  - The specified ``action`` is triggered:
    - ``0`` → raise a breakpoint exception
    - ``1`` → enter debug mode

- Once in debug mode:
  - ``pending`` is cleared
  - ``hit`` is set and remains latched

Key Fields (in ``tdata1``)
~~~~~~~~~~~~~~~~~~~~~~~~~~
- ``count``: Current countdown value.
- ``action``: Determines what to do on match:
  
  - ``0``: Raise a breakpoint exception
  - ``1``: Enter debug mode

- ``m``, ``s``, ``u``: Privilege mode flags — trigger only fires in selected modes.
- ``pending``: Indicates the trigger condition has been met and is awaiting action.
- ``hit``: Latched once the action (break/debug) occurs.

Action Taken on Match
~~~~~~~~~~~~~~~~~~~~~
- Breakpoint (``action == 0``):
  - Sets ``break_from_trigger_d = 1``, which results in:
    - Trap entry
    - Updates to ``mstatus``, ``mepc``, ``mcause``

- Debug Entry (``action == 1``):
  - Sets ``debug_from_trigger_d = 1``, resulting in:
    - Trap into debug mode
    - Updates ``dpc``, ``dcsr``

Pseudocode
~~~~~~~~~~
.. code-block:: text

    If icount trigger is enabled and type is 0x3:
        On instruction execute:
            If in trap handler:
                Hold countdown
            Else if not in trap and count > 0:
                Decrement count
            If count == 0 and privilege matches and not pending:
                Set pending
                If action == 0: raise breakpoint
                If action == 1: enter debug mode
        If breakpoint or debug action occurred:
            Set hit
            Clear pending (for debug)


Mcontrol6
---------
The ``mcontrol6`` trigger detects specific memory accesses (load/store), instruction fetches or execution of specific instructions. It matches on instruction address, instruction, load/store data and load/store addresses. It is the most general and powerful of the trigger types allowing address/data breakpoints, watchpoints, and instruction level filters.

Prerequisites
~~~~~~~~~~~~~~~
- ``SDTRIG`` and ``Mcontrol6`` configuration bits must be enabled.
- Trigger type must be ``4'd6`` in ``tdata1``.

Trigger Match Logic
~~~~~~~~~~~~~~~~~~~
A match occurs if:

1. Privilege Mode Match:
   - One of the flags ``m``, ``s``, ``u`` in ``tdata1`` must match current mode.

2. Condition Match:
   - Based on operation type and mode:
     - Instruction Execute:
       - Match against PC (`commit_instr_i.pc`) or instruction (`orig_instr_i`).
     - Store Operation:
       - Match against store data (`store_result_i`) or address (`vaddr_from_lsu_i`).
     - Load Operation:
       - Match against load result (`commit_instr_i.result`) or load address (`vaddr_from_lsu_i`).

3. Selection Mode:
   - If ``select == 1`` → compare data/instruction value.
   - If ``select == 0`` → compare address.

4. Match Type (`match` field):
   - ``0`` → exact match (``==``)
   - ``1`` → NAPOT (Naturally Aligned Power-of-Two) range match
   - ``8`` → not equal (``!=``)

5. Action (only one supported here):
   - ``1`` → enter debug mode

On match:
- The configured ``action`` is executed.
- In debug mode, internal state is reset:
  - ``hit0`` is cleared
  - ``hit1`` is latched

Key Fields
~~~~~~~~~~
- ``tdata1``:
  - ``execute`` / ``load`` / ``store``: Operation type
  - ``select``: Controls address vs. value comparison
  - ``match``: Match type (exact, NAPOT, not-equal)
  - ``action``: Trigger response (`1` → debug)
  - ``m``, ``s``, ``u``: Privilege filters
  - ``hit0``, ``hit1``: Used to track match state

- ``tdata2``: Match value — can be an address, instruction or data value

Pseudocode
~~~~~~~~~~
.. code-block:: text

    If mcontrol6 is enabled and type is 0x6:
        If privilege level matches tdata1:
            Determine comparison target:
                If execute:
                    If select == 0 → compare PC
                    If select == 1 → compare instruction
                If store:
                    If select == 0 → compare store address
                    If select == 1 → compare store data
                If load:
                    If select == 0 → compare load address
                    If select == 1 → compare load result
            Use match field (==, NAPOT, !=) to evaluate
            If match:
                If action == 1 → enter debug mode
        In debug mode:
            Clear hit0, set hit1, reset trigger state

Implementation Note: Debug Entry Timing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Unlike other trigger types (`icount`, `etrigger`, `itrigger`) which assert debug entry directly at commit stage, the `mcontrol6` trigger initiates debug mode entry via a back-signal to the decode stage.
This difference is necessary because the values used for matching in `mcontrol6` (``orig_instr_i``, ``vaddr_from_lsu_i``, ``store_result_i``) originate from earlier pipeline stages and may not correspond to the instruction currently at the commit point.
To ensure that the correct program counter (``dpc``) is set — specifically, the PC of the instruction being watched or triggering the event — the implementation inserts a pseudo-instruction at the decode stage once a match is detected. This pseudo-instruction proceeds through the pipeline and commits in place of the original instruction.

This approach guarantees:
- The proper instruction is associated with debug entry.
- ``dpc`` reflects the trigger-causing instruction's PC.

This mechanism is only used for `mcontrol6` where precise coordination with the load/store or fetch context is required. Other trigger types do not require this level of staging and use commit-time debug entry.


Etrigger
--------
The ``etrigger`` trigger monitors **exception causes** and fires a trigger action when a matching exception occurs depending on privilege mode. It is highly useful for detecting specific trap causes such as illegal instructions, page faults, breakpoints etc.

Prerequisites
~~~~~~~~~~~~~
- ``SDTRIG`` and ``Etrigger`` configuration bits must be enabled.
- Trigger type must be ``4'd5`` in ``tdata1``.

Trigger Match Logic
~~~~~~~~~~~~~~~~~~~
- The trigger matches and activates when both conditions are met:
   
  - The trigger checks if the current exception cause (`ex_i.cause`) is set in the exception mask stored in ``tdata2``.
  - The current privilege mode (`m`, `s`, `u`) matches what is enabled in ``tdata1``.

- On a match:
  - The normal exception is suppressed.
  - The ``hit`` bit in ``tdata1`` is latched.
  - The specified ``action`` is triggered:
    - ``0`` → raise a breakpoint exception
    - ``1`` → enter debug mode

- While in debug mode, ``hit`` and internal state are cleared.

Key Fields
~~~~~~~~~~
- ``tdata1``:
  - ``action``: Determines the response:
    - ``0``: Raise a breakpoint exception
    - ``1``: Enter debug mode
  - ``m``, ``s``, ``u``: Privilege level flags.
  - ``hit``: Latched on trigger match.

- ``tdata2``: Bitmask for exception causes where each bit corresponds to a cause number. For example:
  - Bit 2 → Illegal instruction
  - Bit 3 → Breakpoint
  - Bit 11 → Environment call from M-mode

Action Taken on Match
~~~~~~~~~~~~~~~~~~~~~
- Breakpoint (``action == 0``):
  - Raises exception via ``break_from_trigger_d = 1``
  - Updates ``mstatus``, ``mepc``, ``mcause``

- Debug Entry (``action == 1``):
  - Sets ``debug_from_trigger_d = 1``
  - Updates ``dpc``, ``dcsr``

Pseudocode
~~~~~~~~~~
.. code-block:: text

    If etrigger is enabled and type is 0x5:
        If current priv level matches trigger (m/s/u):
            If tdata2[exception_cause] is set:
                Mark hit
                If action == 0: raise breakpoint
                If action == 1: enter debug mode
        In debug mode:
            Clear hit and trigger state



Itrigger
--------
The ``itrigger`` trigger monitors **interrupt causes** and fires a trigger action when a matching interrupt occurs at the configured privilege level. This allows catching specific hardware or software interrupt events and take debugging or trapping action immediately.

Prerequisites
~~~~~~~~~~~~~
- ``SDTRIG`` and ``Itrigger`` configuration bits must be enabled.
- Trigger type must be ``4'd4`` in ``tdata1``.

Trigger Match Logic
~~~~~~~~~~~~~~~~~~~
- The trigger matches when both of the following are true:
  
  - The current exception (`ex_i.cause`) is a valid interrupt (i.e., MSB of the cause is set).
  - The lower 5 bits of `ex_i.cause` index into a set bit in the interrupt mask (`tdata2`).
  - Privilege mode matches enabled flags in ``tdata1`` (``m``, ``s``, ``u``).

- On a match:
  - The normal exception is suppressed.
  - The ``hit`` bit is latched.
  - The configured ``action`` is taken:
    - ``0`` → raise a breakpoint exception
    - ``1`` → enter debug mode

- When in debug mode:
  - The ``hit`` bit and trigger state are cleared

Key Fields
~~~~~~~~~~
- ``tdata1``:
  - ``action``: Determines what to do when the interrupt matches:
    - ``0``: Breakpoint
    - ``1``: Debug mode
  - ``m``, ``s``, ``u``: Privilege level match
  - ``hit``: Set on match

- ``tdata2``: Interrupt cause bitmask

Action Taken on Match
~~~~~~~~~~~~~~~~~~~~~
- Breakpoint (``action == 0``):
  - Raises exception via ``break_from_trigger_d = 1``
  - Updates ``mstatus``, ``mepc``, ``mcause``

- Debug Entry (``action == 1``):
  - Sets ``debug_from_trigger_d = 1``
  - Updates ``dpc``, ``dcsr``

Pseudocode
~~~~~~~~~~~~
.. code-block:: text

    If itrigger is enabled and type is 0x4:
        If ex_i.cause[XLEN-1] == 1 (interrupt):
            If tdata2[ex_i.cause[4:0]] is set:
                If current priv level matches tdata1 (m/s/u):
                    Mark hit
                    If action == 0: raise breakpoint
                    If action == 1: enter debug mode
        In debug mode:
            Clear hit and internal match state

