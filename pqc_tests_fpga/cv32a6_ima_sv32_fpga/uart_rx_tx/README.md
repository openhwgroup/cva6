# CVA6 Bare-Metal UART Test (Nexys Video)

This repository contains the hardware-in-the-loop testing pipeline for running bare-metal C applications on a CVA6 (Ariane) 32-bit RISC-V soft core flashed onto a Xilinx Artix-7 Nexys Video FPGA.

Host-to-FPGA communication is handled via the onboard FTDI chip, which provides both the JTAG interface for programming/debugging and a UART interface for I/O.

## Hardware & System Configuration
*   **Target:** CVA6 RISC-V Core on Nexys Video (Artix-7)
*   **System Clock:** 25 MHz
*   **UART Port:** `/dev/ttyUSB0` (Mapped by FTDI Channel B while OpenOCD holds Channel A)
*   **Baud Rate:** 57600 (Derived from 25MHz clock with a UART divisor of `27` / `0x1B`)

## Prerequisites
Ensure the following tools are installed and in your PATH:
*   `openocd`
*   `riscv32-unknown-elf-gdb`
*   `python3` (with `pyserial` installed)

## Execution Workflow

> **⚠️ CRITICAL TIMING WARNING:** 
> The Python host script must be actively listening *before* the FPGA program begins execution. If the FPGA runs first, it will transmit data while the host is disconnected, resulting in missed initialization strings and framing errors . 
> **Follow the exact order below.**

### Step 1: Start OpenOCD
In **Terminal 1**, start the OpenOCD JTAG connection:
```bash
openocd -f corev_apu/fpga/ariane_nexys_video.cfg
```

### Step 2: Connect GDB & Load Binary
In **Terminal 2**, start GDB, connect to OpenOCD, and load the executable into the FPGA's memory:
```bash
riscv32-unknown-elf-gdb test_kyber.elf
```
Inside the GDB prompt:
```gdb
(gdb) target extended-remote localhost:3333
(gdb) load
```
*(Do **not** type `continue` yet. Leave the GDB prompt open.)*

### Step 3: Start the Python Host Script
In **Terminal 3**, launch the host listener. This script will connect to the UART and block until it receives the initialization handshake from the FPGA.
```bash
sudo python3 host_test.py
```
*Expected output:*
`Opening /dev/ttyUSB0 at 57600 baud...`
`Waiting for FPGA to initialize...`

### Step 4: Execute the Code
Return to **Terminal 2** (GDB) and start the RISC-V core:
```gdb
(gdb) continue
```

### Expected Result
Once `continue` is executed, **Terminal 3** should instantly print the clean initialization string, send the raw bytes, and return the computed result:
```text
FPGA says: CVA6 UART INITIALIZED. Awaiting data...

Sending a=1500, b=3500 as raw 32-bit binary bytes...
Waiting for computation result...

--- Returned: Result: 5000 ---
```

## Troubleshooting
* **Garbage characters:** This is a baud rate mismatch or a framing error. Ensure `host_test.py` is set to `57600` baud and that you followed the exact execution order above.
* **Cannot open `/dev/ttyUSB0`:** Ensure you are using `sudo` to run the Python script, or add your user to the `dialout` group. Check your serial port name via `bash pyserial-ports` on any terminal. You can change the parameter in the `host_test.py` to match your port.