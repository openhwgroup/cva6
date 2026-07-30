# Falcon Key Generation Test (`sw_keygen_test`)

This directory contains the bare-metal test harness and execution reports for validating Falcon-512 key generation (`falcon_keygen_make`) on the Hornet RV32IMF soft core.

## Overview

The purpose of this test is to verify the mathematical correctness and memory stability of the processor when executing one of the most computationally heavy operations in Post-Quantum Cryptography. 

Because the Hornet core lacks hardware double-precision floating-point arithmetic (D extension), the Falcon library is compiled with `FALCON_FPEMU 1`. This forces the software to emulate all 64-bit floating-point operations using 32-bit integer instructions. This test successfully proves that the custom linker script (expanding RAM to 1MB) and the software FPU emulation are mathematically sound.

## Source Code Modifications

To run natively in a bare-metal simulator without an underlying operating system, a critical modification was made to the Falcon source code.

### `src/rng.c` (Deterministic PRNG Bypass)
Falcon relies on a system entropy source to seed its internal SHAKE256-based PRNG. Standard implementations use Linux `/dev/urandom` or Windows `CryptGenRandom`, which cause linker or runtime failures in bare-metal environments. 

The `Zf(get_seed)` function in `rng.c` was completely replaced with a deterministic dummy function that populates the buffer sequentially. This ensures the key generation does not abort due to lack of entropy and provides deterministic, repeatable known-answer tests (KATs) for simulator verification.

```c
/* HORNET BARE-METAL PATCH */
int Zf(get_seed)(void *seed, size_t len) {
    uint8_t *buf = (uint8_t *)seed;
    if (len == 0) return 1;
    for (size_t i = 0; i < len; i++) {
        buf[i] = (uint8_t)(i & 0xFF);
    }
    return 1; // 1 means success
}
```
## Simulation Execution

The test was executed using the **Cadence Xcelium** simulation environment. To maximize simulation performance for the millions of instructions required, waveform dumping was disabled.

### Xcelium Run Script (`run_sim.sh`)
```bash
#!/bin/bash

# Clear out any old simulation data
rm -rf xcelium.d xrun.log xrun.history

echo "Starting Xcelium RTL Simulation..."

# Run the simulation
xrun \
  -clean \
  -64bit \
  -sv \
  -timescale 1ns/1ps \
  +nospecify \
  +notimingchecks \
  -l xrun.log \
  ../../source/sources_1/imports/src/*.v \
  ../../source/sim_1/imports/sim_src/barebones_top_tb.v
  ```
  ## Results & Performance Analysis

The simulation successfully generated the keys and triggered the success debug signal (`*DEBUG_REG = 'P'`).

**Raw Xcelium Output:**
```text
Non-determined data:    S	 Time:   0.02 ms
...
--> Simulation Progress: 4100.00 ms
Success!	 Finished at:4102.28 ms

Simulation complete via $finish(1) at time 4102275637500 PS + 2
/home/tekiny/xcellium_projects/hornet/HORNET-RV32IMF/source/sources_1/imports/src/debug_interface_wb.v:38 				$finish();
xcelium> exit
TOOL:	xrun(64)	22.03-s005: Exiting on Jul 02, 2026 at 09:01:50 EDT  (total: 00:43:33)
```
### Cycle Calculation

The core was simulated with a **40 MHz clock** (25 ns per clock cycle).

* **Simulated Processor Time:** `4102.28 ms` (4.102 seconds)
* **Real-World Wall-Clock Time:** `43 minutes, 33 seconds`
* **Total Clock Cycles:** `4.10228 seconds * 40,000,000 cycles/second ≈ 164,091,200 cycles`
