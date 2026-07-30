# CVA6 Bare-Metal Kyber KEM Test (Nexys Video)

This repository contains the hardware-in-the-loop testing pipeline for running and validating bare-metal Post-Quantum Cryptography (Kyber KEM) C applications on a CVA6 (Ariane) 32-bit RISC-V soft core flashed onto a Xilinx Artix-7 Nexys Video FPGA.

Host-to-FPGA communication is handled via the onboard FTDI chip, which provides both the JTAG interface for programming/debugging and a UART interface for I/O. The test utilizes a host-device synchronization protocol to ensure no UART data is lost during the initialization phase.

## Repository Structure
*   `main.c`: Bare-metal C code running the Kyber Key Encapsulation Mechanism validation.
*   `host_test.py`: Python host script that synchronizes with the FPGA and logs the test output.
*   `load.elf`: Compiled RISC-V binary.
*   `link.ld` / `Makefile`: Linker script and build instructions for the bare-metal environment.

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

> **⚠️ SYNCHRONIZATION NOTE:** 
> The C code is designed to block execution until it receives a `'c'` trigger character from the host. While this prevents desynchronization, it is still highly recommended to start the Python listener *before* resuming the FPGA to ensure the initialization string is caught perfectly.
> **Follow the exact order below.**

### Step 1: Start OpenOCD
In **Terminal 1**, start the OpenOCD JTAG connection:

    openocd -f corev_apu/fpga/ariane_nexys_video.cfg

### Step 2: Connect GDB & Load Binary
In **Terminal 2**, start GDB, connect to OpenOCD, and load the executable into the FPGA's memory:

    riscv32-unknown-elf-gdb load.elf

Inside the GDB prompt:

    (gdb) target extended-remote localhost:3333
    (gdb) load

*(Do **not** type `continue` yet. Leave the GDB prompt open.)*

### Step 3: Start the Python Host Script
In **Terminal 3**, launch the host listener. This script will connect to the UART, wait for the initialization string, and automatically send the trigger character.

    sudo python3 host_test.py

*Expected output:*

    Opening /dev/ttyUSB0 at 57600 baud...
    Waiting for FPGA to initialize...

### Step 4: Execute the Code
Return to **Terminal 2** (GDB) and start the RISC-V core:

    (gdb) continue

### Expected Result
Once `continue` is executed, **Terminal 3** should instantly print the clean initialization string, send the trigger, run the Kyber tests, and gracefully close the connection:

    FPGA: CVA6 UART INITIALIZED. Waiting for trigger...

    Triggering Kyber test on FPGA...

    --- Test Output ---

    ===============================
     Kyber KEM FPGA Hardware Test
    ===============================

    --- Running Test Iteration 1 ---
    Generating keypair...
    Encapsulating secret...
    Decapsulating secret...
    Shared secrets match.
    Invalid secret key rejected correctly.
    Invalid ciphertext rejected correctly.

    ALL TESTS PASSED
    CRYPTO_PUBLICKEYBYTES = 1184
    CRYPTO_SECRETKEYBYTES = 2400
    CRYPTO_CIPHERTEXTBYTES = 1088
    CRYPTO_BYTES = 32

    Serial connection closed.

## Troubleshooting
* **Garbage characters:** This is a baud rate mismatch or a framing error. Ensure `host_test.py` is set to `57600` baud and that you are using a 25MHz system clock on the FPGA.
* **Cannot open `/dev/ttyUSB0`:** Ensure you are using `sudo` to run the Python script, or add your user to the `dialout` group. Check your serial port name via `bash pyserial-ports` on any terminal. You can change the port parameter inside `host_test.py` to match your system.