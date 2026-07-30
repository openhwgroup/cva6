# FPGA Tests

**WORK IN PROGRESS!** This sub-directory will fulfill all the required scripts, linkers and main C codes for real-time FPGA implementation and tests. 

This guide outlines how to establish a JTAG connection to the CVA6 soft core on the FPGA using OpenOCD and how to load and execute compiled `.elf` binaries.

---

## Project Status & To-Do

| Task / Objective | Associated Folder | Status |
| :--- | :--- | :--- |
| JTAG Bring-up & GDB Execution | `kyber_gdb` | ✅ **Done** |
| Basic UART pipeline (Receive `a`, `b`, transmit `c = a+b` with "Result:") | `uart_rx_tx` | ✅ **Done** |
| Fully run Kyber over UART | `kyber_uart` | ✅ **Done** |
| Fully run Kyber, count clock cycles, and print cycles to host | `kyber_all` | ✅ **Done** |
| Fully run Dilithium, count clock cycles, and print cycles to host | `dilithium_all` | ✅ **Done** |
| Fully run Falcon, count clock cycles, and print cycles to host | `falcon_all` | ✅ **Done** | 


Eventhough Every test folder has its own READMEs, the general concept of usign OpenOCD and GDB (GNU Debugger) is explained below.

---

## Step 1: Establish the OpenOCD Connection

Before you can load code or debug, you must open a connection to the FPGA and halt the CPU. This exposes a port that GDB can connect to.

> **Warning:** Do not install OpenOCD inside the Docker environment. It must reach the localhost ports, which may cause a problem for some users. 

Open a terminal and run OpenOCD using the provided configuration file:

```bash
openocd -f corev_apu/fpga/ariane_nexys_video.cfg
```

If successful, OpenOCD will halt the core and begin listening for GDB connections on port `3333`. Your output should look similar to this:

```text
Open On-Chip Debugger 0.12.0+dev-02603-gfc566d740 (2026-07-24-09:53)
Licensed under GNU GPL v2
For bug reports, read
	[http://openocd.org/doc/doxygen/bugs.html](http://openocd.org/doc/doxygen/bugs.html)
DEPRECATED! use 'riscv virt2phys_mode' not 'riscv set_enable_virtual'
Warning: This version of OpenOCD does not support address translation. To debug on virtual addresses, please update to the latest version.
Info : clock speed 1000 kHz
Info : JTAG tap: riscv.cpu tap/device found: 0x00000001 (mfg: 0x000 (<invalid>), part: 0x0000, ver: 0x0)
Info : [riscv.cpu] datacount=2 progbufsize=8
Info : [riscv.cpu] Examined RISC-V core
Info : [riscv.cpu]  XLEN=32, misa=0x40141101
Info : [riscv.cpu] Examination succeed
Info : [riscv.cpu] starting gdb server on 3333
Info : Listening on port 3333 for gdb connections
riscv.cpu halted due to debug-request.
Ready for Remote Connections
Info : Listening on port 6666 for tcl connections
Info : Listening on port 4444 for telnet connections
```

**Leave this terminal running in the background.** 

---

## Step 2: Choose Your Execution Method

Depending on your goal, you can either step through your code interactively using GDB, or you can push the code directly to the board and let it run continuously.

### Method A: Interactive Debugging with GDB

Open a **new terminal** (or your Docker container) and launch the RISC-V GDB tool, passing it your compiled binary:

```bash
riscv32-unknown-elf-gdb <your_compiled_test>.elf
```

Once inside the `(gdb)` prompt, connect to the OpenOCD server you started in Step 1, load the code into the FPGA's memory, and start debugging:

```gdb
# Connect to OpenOCD (Use host.docker.internal:3333 if running GDB from a Docker container)
(gdb) target extended-remote localhost:3333

# Flash the binary into the FPGA's memory (You can do this if you want to reset the program as well)
(gdb) load

# Set a breakpoint at the start of your program (This is optional)
(gdb) break main

# Execute
(gdb) continue
```

From here, you can use standard GDB commands like `step` (step by line), `stepi` (step by instruction), or `info registers` to inspect the CPU state.

### Method B: Run Without Debugging

If you simply want to load a test program and let it run continuously (for example, to interact with it via a UART serial terminal) without keeping GDB open, you can pass a single command string directly to OpenOCD. 

#### Step 1: Connect GDB & Load Binary
In **Terminal 2**, start GDB, connect to OpenOCD, and load the executable into the FPGA's memory:

    riscv32-unknown-elf-gdb load.elf

Inside the GDB prompt:

    (gdb) target extended-remote localhost:3333
    (gdb) load

*(Do **not** type `continue` yet. Leave the GDB prompt open.)*

#### Step 2: Start the Python Host Script
In **Terminal 3**, launch the host listener. This script will connect to the UART, wait for the initialization string, and automatically send the trigger character.

    sudo python3 host_test.py

*Expected output:*

    Opening /dev/ttyUSB0 at 57600 baud...
    Waiting for FPGA to initialize...

#### Step 3: Execute the Code
Return to **Terminal 2** (GDB) and start the RISC-V core:

    (gdb) continue

#### Expected Result
Once `continue` is executed, **Terminal 3** should instantly print the clean initialization string, send the trigger, run the according test.

#### Troubleshooting
* **Garbage characters:** This is a baud rate mismatch or a framing error. Ensure `host_test.py` is set to `57600` baud and that you are using a 25MHz system clock on the FPGA.
* **Cannot open `/dev/ttyUSB0`:** Ensure you are using `sudo` to run the Python script, or add your user to the `dialout` group. Check your serial port name via `bash pyserial-ports` on any terminal. You can change the port parameter inside `host_test.py` to match your system.
