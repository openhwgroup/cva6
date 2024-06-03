<!--Copyright (c) 2024 OpenHW Group
Copyright (c) 2024 Thales
SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1 
Author: Abdessamii Oukalrazqou
-->

# csr



## Registers Summary

|Address|Register Name|Description|
| :--- | :--- | :--- |
|0x300|[MSTATUS](#MSTATUS)|The mstatus register keeps track of and controls the hart’s current operating state.|
|0x300|[MSTATUSH](#MSTATUSH)|The mstatush register keeps track of and controls the hart’s current operating state.|
|0x301|[MISA](#MISA)|misa is a read-write register reporting the ISA supported by the hart.|
|0x304|[MIE](#MIE)|The mie register is an MXLEN-bit read/write register containing interrupt enable bits.|
|0x305|[MTVEC](#MTVEC)|MXLEN-bit read/write register that holds trap vector configuration.|
|0x323-0x33f|[MHPMEVENT[3-31]](#MHPMEVENT[3-31])|The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3.|
|0x340|[MSCRATCH](#MSCRATCH)|The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode.|
|0x341|[MEPC](#MEPC)|The mepc is a warl register that must be able to hold all valid physical and virtual addresses.|
|0x342|[MCAUSE](#MCAUSE)|The mcause register stores the information regarding the trap.|
|0x343|[MTVAL](#MTVAL)|The mtval is a warl register that holds the address of the instruction which caused the exception.|
|0x344|[MIP](#MIP)|The mip register is an MXLEN-bit read/write register containing information on pending interrupts.|
|0x3a0-0x3a1|[PMPCFG[0-1]](#PMPCFG[0-1])|PMP configuration register|
|0x3b0-0x3b7|[PMPADDR[0-7]](#PMPADDR[0-7])|Physical memory protection address register|
|0xb00|[MCYCLE](#MCYCLE)|Counts the number of clock cycles executed from an arbitrary point in time.|
|0xb02|[MINSTRET](#MINSTRET)|Counts the number of instructions completed from an arbitrary point in time.|
|0xb03-0xb1f|[MHPMCOUNTER[3-31]](#MHPMCOUNTER[3-31])|The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode.|
|0xb80|[MCYCLEH](#MCYCLEH)|upper 32 bits of mcycle|
|0xb82|[MINSTRETH](#MINSTRETH)|Upper 32 bits of minstret.|
|0xb83-0xb9f|[MHPMCOUNTER[3-31]H](#MHPMCOUNTER[3-31]H)|The mhpmcounterh returns the upper half word in RV32I systems.|
|0xf11|[MVENDORID](#MVENDORID)|32-bit read-only register providing the JEDEC manufacturer ID of the provider of the core.|
|0xf12|[MARCHID](#MARCHID)|MXLEN-bit read-only register encoding the base microarchitecture of the hart.|
|0xf13|[MIMPID](#MIMPID)|Provides a unique encoding of the version of the processor implementation.|
|0xf14|[MHARTID](#MHARTID)|MXLEN-bit read-only register containing the integer ID of the hardware thread running the code.|

### Registers Description

#### MSTATUS
  
---  
**Address** 0x300  
**Reset Value** 0x1800  
**Privilege Mode** M  
**Description** The mstatus register keeps track of and controls the hart’s current operating state.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|0|UIE||0x0|WARL|Stores the state of the user mode interrupts.|
|1|SIE||0x0|WARL|Stores the state of the supervisor mode interrupts.|
|2|RESERVED_2||0x0|WPRI|RESERVED|
|3|MIE|[0 , 1]|0x0|WLRL|Stores the state of the machine mode interrupts.|
|4|UPIE||0x0|WARL|Stores the state of the user mode interrupts prior to the trap.|
|5|SPIE||0x0|WARL|Stores the state of the supervisor mode interrupts prior to the trap.|
|6|RESERVED_6||0x0|WPRI|RESERVED|
|7|MPIE|[0 , 1]|0x0|WLRL|Stores the state of the machine mode interrupts prior to the trap.|
|8|SPP||0x0|WARL|Stores the previous priority mode for supervisor.|
|[10:9]|RESERVED_9||0x0|WPRI|RESERVED|
|[12:11]|MPP|[0x3]|0x3|WARL|Stores the previous priority mode for machine.|
|[14:13]|FS||0x0|WARL|Encodes the status of the floating-point unit, including the CSR fcsr and floating-point data registers.|
|[16:15]|XS||0x0|WARL|Encodes the status of additional user-mode extensions and associated state.|
|17|MPRV||0x0|WARL|Modifies the privilege level at which loads and stores execute in all privilege modes.|
|18|SUM||0x0|WARL|Modifies the privilege with which S-mode loads and stores access virtual memory.|
|19|MXR||0x0|WARL|Modifies the privilege with which loads access virtual memory.|
|20|TVM||0x0|WARL|Supports intercepting supervisor virtual-memory management operations.|
|21|TW||0x0|WARL|Supports intercepting the WFI instruction.|
|22|TSR||0x0|WARL|Supports intercepting the supervisor exception return instruction.|
|23|SPELP||0x0|WARL|Supervisor mode previous expected-landing-pad (ELP) state.|
|[30:24]|RESERVED_24||0x0|WPRI|RESERVED|
|31|SD||0x0|WARL|Read-only bit that summarizes whether either the FS field or XS field signals the presence of some dirty state.|

#### MSTATUSH
  
---  
**Address** 0x300  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mstatush register keeps track of and controls the hart’s current operating state.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[3:0]|RESERVED_0||0x0|WPRI|RESERVED|
|4|SBE||0x0|WARL|control the endianness of memory accesses other than instruction fetches for supervisor mode|
|5|MBE||0x0|WARL|control the endianness of memory accesses other than instruction fetches for machine mode|
|6|GVA||0x0|WARL|Stores the state of the supervisor mode interrupts.|
|7|MPV||0x0|WARL|Stores the state of the user mode interrupts.|
|8|RESERVED_8||0x0|WPRI|RESERVED|
|9|MPELP||0x0|WARL|Machine mode previous expected-landing-pad (ELP) state.|
|[31:10]|RESERVED_10||0x0|WPRI|RESERVED|

#### MISA
  
---  
**Address** 0x301  
**Reset Value** 0x40001106  
**Privilege Mode** M  
**Description** misa is a read-write register reporting the ISA supported by the hart.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[25:0]|EXTENSIONS|[0x0000000:0x3FFFFFF]|0x1106|WARL|Encodes the presence of the standard extensions, with a single bit per letter of the alphabet.|
|[29:26]|RESERVED_26||0x0|WPRI|RESERVED|
|[31:30]|MXL|[0x1]|0x1|WARL|Encodes the native base integer ISA width.|

#### MIE
  
---  
**Address** 0x304  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mie register is an MXLEN-bit read/write register containing interrupt enable bits.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|0|USIE||0x0|WARL|User Software Interrupt enable.|
|1|SSIE||0x0|WARL|Supervisor Software Interrupt enable.|
|2|VSSIE||0x0|WARL|VS-level Software Interrupt enable.|
|3|MSIE|[0x0 , 0x1]|0x0|WLRL|Machine Software Interrupt enable.|
|4|UTIE||0x0|WARL|User Timer Interrupt enable.|
|5|STIE||0x0|WARL|Supervisor Timer Interrupt enable.|
|6|VSTIE||0x0|WARL|VS-level Timer Interrupt enable.|
|7|MTIE|[0 , 1]|0x0|WLRL|Machine Timer Interrupt enable.|
|8|UEIE||0x0|WARL|User External Interrupt enable.|
|9|SEIE||0x0|WARL|Supervisor External Interrupt enable.|
|10|VSEIE||0x0|WARL|VS-level External Interrupt enable.|
|11|MEIE|[0 , 1]|0x0|WLRL|Machine External Interrupt enable.|
|12|SGEIE||0x0|WARL|HS-level External Interrupt enable.|
|[31:13]|RESERVED_13||0x0|WPRI|RESERVED|

#### MTVEC
  
---  
**Address** 0x305  
**Reset Value** 0x80010000  
**Privilege Mode** M  
**Description** MXLEN-bit read/write register that holds trap vector configuration.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[1:0]|MODE|[0x0]|0x0|WARL|Vector mode.|
|[31:2]|BASE|[0x3FFFFFFF, 0x00000000]|0x20004000|WARL|Vector base address.|

#### MHPMEVENT[3-31]
  
---  
**Address** 0x323-0x33f  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MHPMEVENT[I]|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3.|

#### MSCRATCH
  
---  
**Address** 0x340  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MSCRATCH|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode.|

#### MEPC
  
---  
**Address** 0x341  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mepc is a warl register that must be able to hold all valid physical and virtual addresses.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MEPC|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|The mepc is a warl register that must be able to hold all valid physical and virtual addresses.|

#### MCAUSE
  
---  
**Address** 0x342  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mcause register stores the information regarding the trap.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[30:0]|EXCEPTION_CODE|[0 , 15]|0x0|WLRL|Encodes the exception code.|
|31|INTERRUPT|[0x0 , 0x1]|0x0|WLRL|Indicates whether the trap was due to an interrupt.|

#### MTVAL
  
---  
**Address** 0x343  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mtval is a warl register that holds the address of the instruction which caused the exception.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MTVAL|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|The mtval is a warl register that holds the address of the instruction which caused the exception.|

#### MIP
  
---  
**Address** 0x344  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mip register is an MXLEN-bit read/write register containing information on pending interrupts.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|0|USIP||0x0|WARL|User Software Interrupt Pending.|
|1|SSIP||0x0|WARL|Supervisor Software Interrupt Pending.|
|2|VSSIP||0x0|WARL|VS-level Software Interrupt Pending.|
|3|MSIP|0x1|0x0|RO_VARIABLE|Machine Software Interrupt Pending.|
|4|UTIP||0x0|WARL|User Timer Interrupt Pending.|
|5|STIP||0x0|WARL|Supervisor Timer Interrupt Pending.|
|6|VSTIP||0x0|WARL|VS-level Timer Interrupt Pending.|
|7|MTIP|0x1|0x0|RO_VARIABLE|Machine Timer Interrupt Pending.|
|8|UEIP||0x0|WARL|User External Interrupt Pending.|
|9|SEIP||0x0|WARL|Supervisor External Interrupt Pending.|
|10|VSEIP||0x0|WARL|VS-level External Interrupt Pending.|
|11|MEIP|0x1|0x0|RO_VARIABLE|Machine External Interrupt Pending.|
|12|SGEIP||0x0|WARL|HS-level External Interrupt Pending.|
|[31:13]|RESERVED_13||0x0|WPRI|RESERVED|

#### PMPCFG[0-1]
  
---  
**Address** 0x3a0-0x3a1  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** PMP configuration register
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[7:0]|PMP[I*4 + 0]CFG|[0x00:0xFF]|0x0|WARL|pmp configuration bits|
|[15:8]|PMP[I*4 + 1]CFG|[0x00:0xFF]|0x0|WARL|pmp configuration bits|
|[23:16]|PMP[I*4 + 2]CFG|[0x00:0xFF]|0x0|WARL|pmp configuration bits|
|[31:24]|PMP[I*4 + 3]CFG|[0x00:0xFF]|0x0|WARL|pmp configuration bits|

#### PMPADDR[0-7]
  
---  
**Address** 0x3b0-0x3b7  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** Physical memory protection address register
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|PMPADDR[I]|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|Physical memory protection address register|

#### MCYCLE
  
---  
**Address** 0xb00  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** Counts the number of clock cycles executed from an arbitrary point in time.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MCYCLE|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|Counts the number of clock cycles executed from an arbitrary point in time.|

#### MINSTRET
  
---  
**Address** 0xb02  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** Counts the number of instructions completed from an arbitrary point in time.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MINSTRET|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|Counts the number of instructions completed from an arbitrary point in time.|

#### MHPMCOUNTER[3-31]
  
---  
**Address** 0xb03-0xb1f  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MHPMCOUNTER[I]|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode.|

#### MCYCLEH
  
---  
**Address** 0xb80  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** upper 32 bits of mcycle
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MCYCLEH|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|upper 32 bits of mcycle|

#### MINSTRETH
  
---  
**Address** 0xb82  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** Upper 32 bits of minstret.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MINSTRETH|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|Upper 32 bits of minstret.|

#### MHPMCOUNTER[3-31]H
  
---  
**Address** 0xb83-0xb9f  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** The mhpmcounterh returns the upper half word in RV32I systems.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MHPMCOUNTER[I]H|[0x00000000 , 0xFFFFFFFF]|0x00000000|WARL|The mhpmcounterh returns the upper half word in RV32I systems.|

#### MVENDORID
  
---  
**Address** 0xf11  
**Reset Value** 0x602  
**Privilege Mode** M  
**Description** 32-bit read-only register providing the JEDEC manufacturer ID of the provider of the core.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MVENDORID|0x00000602|0x00000602|RO_CONSTANT|32-bit read-only register providing the JEDEC manufacturer ID of the provider of the core.|

#### MARCHID
  
---  
**Address** 0xf12  
**Reset Value** 0x3  
**Privilege Mode** M  
**Description** MXLEN-bit read-only register encoding the base microarchitecture of the hart.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MARCHID|0x00000003|0x00000003|RO_CONSTANT|MXLEN-bit read-only register encoding the base microarchitecture of the hart.|

#### MIMPID
  
---  
**Address** 0xf13  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** Provides a unique encoding of the version of the processor implementation.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MIMPID|0x00000000|0x00000000|RO_CONSTANT|Provides a unique encoding of the version of the processor implementation.|

#### MHARTID
  
---  
**Address** 0xf14  
**Reset Value** 0x0  
**Privilege Mode** M  
**Description** MXLEN-bit read-only register containing the integer ID of the hardware thread running the code.
|Bits|Field Name|Legal Values|Reset|Type|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|MHARTID|0x00000000|0x00000000|RO_CONSTANT|MXLEN-bit read-only register containing the integer ID of the hardware thread running the code.|
