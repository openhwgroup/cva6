# TB_RISCV: VERIFICATION ENVIRONMENT FOR THE PULP CORES

Verification environment for the PULP RI5CY cores is implemented.

## Description

The top file of this repository is called `tb_riscv_core.sv`. The input and output signals of this unit are the same as RI5CY.
It includes the following components:
  - The core instance
  - The instance of the perturbation module, that is described in the file `riscv_perturbation.sv`.
  This programmable unit is able to introduce stalls on the memory interfaces and to generate interrupts requests. This is accomplished with the units `riscv_random_stall.sv` and `riscv_random_interrupt_generator.sv`, for stalls and interrupts respectively.
  - The instance of the simulation checker is used to check the functional correctness of the core, you should set to 1 the parameter SIMCHECKER in the parameters list of the `tb_riscv_core.sv`.

## How to set up the perturbation module

The perturbation module is programmable. It contains a set of memory-mapped registers used to program the module according to the user needs. These registers are mapped in the debug unit address space, and the same buses of the debug unit are used to read and write those registers.

#### How to set up the stalls generators

Since both the instruction and data stalls generators are instances of the same unit, they are configured with the same steps.

1) The default mode does not introduce any stalls on the interface. The input of the units are directly forwarded to the output ports.

2) The mode STANDARD will introduce a fixed number of stalls on the specified signals of the desired interface.

3) The mode RANDOM will randomly injects stalls on the desired interface.

#### How to set up the interrupt generator

As for the stalls generators, the interrupt generator can be easily programmed with load and store instructions. Again, three working modes are supported:

1) The default mode does not generate any interrupt request. The input of the module, coming from the event unit and the core, are simply forwarded to the output ports. This allows the external peripherals to eventually raise interrupt requests.

2) The mode RANDOM will randomize on the generation of interrupt requests. In particular, the module randomizes on both the number of stalls that separate two consecutive interrupt requests, as well as on the interrupt causes.

3) The mode PC_TRIG is about raising an interrupt request when the value of the program counter, taken from the ID stage of the core, is equal to the value stored in a proper perturbation register. For this interrupt cause, the identifier 18 is reserved.

Following an example to directly use the Assembler to set up the interrupt generator working with the PC-triggered mode:

```
la %[pc_trig],  pc_label;
sw %[pc_trig],  0(%[perturbation_reg_addr]);
sw %[irq_mode], 0(%[perturbation_mode_addr]);
....
pc_label: nop;
....
```

In the previous example, `pc_label` represents the instruction address at which the interrupt request will be raised (i.e. when the `nop` instruction is in the ID stage of the core).
The address is stored in the perturbation register and The PC_TRIG mode is set via the last store instruction.

## TODO:

The simulation checker should be used yet. It is under development.