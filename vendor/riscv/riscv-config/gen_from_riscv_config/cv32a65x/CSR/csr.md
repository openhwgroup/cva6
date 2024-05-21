
# CV32A65X CSR Documentation



## Registers Summary

|Address|Register Name|Description|
| :--- | :--- | :--- |
|0x300|[mstatus](#mstatus)|The mstatus register keeps track of and controls the hart’s current operating state.|
|0x300|[mstatush](#mstatush)|The mstatush register keeps track of and controls the hart’s current operating state.|
|0x301|[misa](#misa)|misa is a read-write register reporting the ISA supported by the hart.|
|0x304|[mie](#mie)|The mie register is an MXLEN-bit read/write register containing interrupt enable bits.|
|0x305|[mtvec](#mtvec)|MXLEN-bit read/write register that holds trap vector configuration.|
|0x320|[mcountinhibit](#mcountinhibit)|The mcountinhibit is a 32-bit WARL register that controls which of the hardware performance-monitoring counters increment.|
|0x323-0x33f|[mhpmevent[3-31]](#mhpmevent[3-31])|The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3.|
|0x340|[mscratch](#mscratch)|The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode.|
|0x341|[mepc](#mepc)|The mepc is a warl register that must be able to hold all valid physical and virtual addresses.|
|0x342|[mcause](#mcause)|The mcause register stores the information regarding the trap.|
|0x343|[mtval](#mtval)|The mtval is a warl register that holds the address of the instruction which caused the exception.|
|0x344|[mip](#mip)|The mip register is an MXLEN-bit read/write register containing information on pending interrupts.|
|0x3a0-0x3af|[pmpcfg[0-15]](#pmpcfg[0-15])|PMP configuration register|
|0x3b0-0x3ef|[pmpaddr[0-63]](#pmpaddr[0-63])|Physical memory protection address register|
|0xb00|[mcycle](#mcycle)|Counts the number of clock cycles executed from an arbitrary point in time.|
|0xb02|[minstret](#minstret)|Counts the number of instructions completed from an arbitrary point in time.|
|0xb03-0xb1f|[mhpmcounter[3-31]](#mhpmcounter[3-31])|The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode.|
|0xb80|[mcycleh](#mcycleh)|upper 32 bits of mcycle|
|0xb82|[minstreth](#minstreth)|Upper 32 bits of minstret.|
|0xb83-0xb9f|[mhpmcounter[3-31]h](#mhpmcounter[3-31]h)|The mhpmcounterh returns the upper half word in RV32I systems.|
|0xf11|[mvendorid](#mvendorid)||
|0xf12|[marchid](#marchid)|MXLEN-bit read-only register encoding the base microarchitecture of the hart.|
|0xf13|[mimpid](#mimpid)|Provides a unique encoding of the version of the processor implementation.|
|0xf14|[mhartid](#mhartid)|MXLEN-bit read-only register containing the integer ID of the hardware thread running the code.|

### Registers Description

#### mstatus
  
---  
**Address** 0x300  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mstatus register keeps track of and controls the hart’s current operating state.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|0|uie|||RW|Stores the state of the user mode interrupts.|
|1|sie|||RW|Stores the state of the supervisor mode interrupts.|
|3|mie|0|1|RW|Stores the state of the machine mode interrupts.|
|4|upie|||RW|Stores the state of the user mode interrupts prior to the trap.|
|5|spie|||RW|Stores the state of the supervisor mode interrupts prior to the trap.|
|7|mpie|0|1|RW|Stores the state of the machine mode interrupts prior to the trap.|
|8|spp|||RW|Stores the previous priority mode for supervisor.|
|[12:11]|mpp|0x0|0x3|RW|Stores the previous priority mode for machine.|
|[14:13]|fs|||RW|Encodes the status of the floating-point unit, including the CSR fcsr and floating-point data registers.|
|[16:15]|xs|0x1|0|RW|Encodes the status of additional user-mode extensions and associated state.|
|17|mprv|||RW|Modifies the privilege level at which loads and stores execute in all privilege modes.|
|18|sum|||RW|Modifies the privilege with which S-mode loads and stores access virtual memory.|
|19|mxr|||RW|Modifies the privilege with which loads access virtual memory.|
|20|tvm|||RW|Supports intercepting supervisor virtual-memory management operations.|
|21|tw|||RW|Supports intercepting the WFI instruction.|
|22|tsr|||RW|Supports intercepting the supervisor exception return instruction.|
|23|spelp|||RW|Supervisor mode previous expected-landing-pad (ELP) state.|
|31|sd|||RW|Read-only bit that summarizes whether either the FS field or XS field signals the presence of some dirty state.|
|[30:24]|Reserved_24|||Reserved|Reserved|

#### mstatush
  
---  
**Address** 0x300  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mstatush register keeps track of and controls the hart’s current operating state.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|4|sbe|||RW|control the endianness of memory accesses other than instruction fetches for supervisor mode|
|5|mbe|||RW|control the endianness of memory accesses other than instruction fetches for machine mode|
|6|gva|||RW|Stores the state of the supervisor mode interrupts.|
|7|mpv|||RW|Stores the state of the user mode interrupts.|
|9|mpelp|||RW|Machine mode previous expected-landing-pad (ELP) state.|
|[31:10]|Reserved_10|||Reserved|Reserved|

#### misa
  
---  
**Address** 0x301  
**Reset Value**0x40001104  
**Priviliege mode** M  
**Description** misa is a read-write register reporting the ISA supported by the hart.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[25:0]|extensions|0x0000000|0x3FFFFFF|RW|Encodes the presence of the standard extensions, with a single bit per letter of the alphabet.|
|[31:30]|mxl|0x1|None||Encodes the native base integer ISA width.|
|[29:26]|Reserved_26|||Reserved|Reserved|

#### mie
  
---  
**Address** 0x304  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mie register is an MXLEN-bit read/write register containing interrupt enable bits.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|0|usie|||RW|User Software Interrupt enable.|
|1|ssie|||RW|Supervisor Software Interrupt enable.|
|2|vssie|||RW|VS-level Software Interrupt enable.|
|3|msie|0x0|0x1|RW|Machine Software Interrupt enable.|
|4|utie|||RW|User Timer Interrupt enable.|
|5|stie|||RW|Supervisor Timer Interrupt enable.|
|6|vstie|||RW|VS-level Timer Interrupt enable.|
|7|mtie|0|1|RW|Machine Timer Interrupt enable.|
|8|ueie|||RW|User External Interrupt enable.|
|9|seie|||RW|Supervisor External Interrupt enable.|
|10|vseie|||RW|VS-level External Interrupt enable.|
|11|meie|0|1|RW|Machine External Interrupt enable.|
|12|sgeie|||RW|HS-level External Interrupt enable.|
|[31:13]|Reserved_13|||Reserved|Reserved|

#### mtvec
  
---  
**Address** 0x305  
**Reset Value**0x80010000  
**Priviliege mode** M  
**Description** MXLEN-bit read/write register that holds trap vector configuration.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[1:0]|mode|0x0|0x1|RW|Vector mode.|
|[31:2]|base|0x3FFFFFFF|0x00000000|RW|Vector base address.|

#### mcountinhibit
  
---  
**Address** 0x320  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mcountinhibit is a 32-bit WARL register that controls which of the hardware performance-monitoring counters increment.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mcountinhibit|0x00000000|0xFFFFFFFF|RW|The mcountinhibit is a 32-bit WARL register that controls which of the hardware performance-monitoring counters increment.|

#### mhpmevent[3-31]
  
---  
**Address** 0x323-0x33f  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mhpmevent[i]|0x00000000|0xFFFFFFFF|RW|The mhpmevent is a MXLEN-bit event register which controls mhpmcounter3.|

#### mscratch
  
---  
**Address** 0x340  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mscratch|0x00000000|0xFFFFFFFF|RW|The mscratch register is an MXLEN-bit read/write register dedicated for use by machine mode.|

#### mepc
  
---  
**Address** 0x341  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mepc is a warl register that must be able to hold all valid physical and virtual addresses.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mepc|0x00000000|0xFFFFFFFF|RW|The mepc is a warl register that must be able to hold all valid physical and virtual addresses.|

#### mcause
  
---  
**Address** 0x342  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mcause register stores the information regarding the trap.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[30:0]|exception_code|0|15|RW|Encodes the exception code.|
|31|interrupt|0x0|0x1|RW|Indicates whether the trap was due to an interrupt.|

#### mtval
  
---  
**Address** 0x343  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mtval is a warl register that holds the address of the instruction which caused the exception.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mtval|0x00000000|0xFFFFFFFF|RW|The mtval is a warl register that holds the address of the instruction which caused the exception.|

#### mip
  
---  
**Address** 0x344  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mip register is an MXLEN-bit read/write register containing information on pending interrupts.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|0|usip|||RW|User Software Interrupt Pending.|
|1|ssip|||RW|Supervisor Software Interrupt Pending.|
|2|vssip|||RW|VS-level Software Interrupt Pending.|
|3|msip|0x1|0|RW|Machine Software Interrupt Pending.|
|4|utip|||RW|User Timer Interrupt Pending.|
|5|stip|||RW|Supervisor Timer Interrupt Pending.|
|6|vstip|||RW|VS-level Timer Interrupt Pending.|
|7|mtip|0x1|0|RW|Machine Timer Interrupt Pending.|
|8|ueip|||RW|User External Interrupt Pending.|
|9|seip|||RW|Supervisor External Interrupt Pending.|
|10|vseip|||RW|VS-level External Interrupt Pending.|
|11|meip|0x1|0|RW|Machine External Interrupt Pending.|
|12|sgeip|||RW|HS-level External Interrupt Pending.|
|[31:13]|Reserved_13|||Reserved|Reserved|

#### pmpcfg[0-15]
  
---  
**Address** 0x3a0-0x3af  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** PMP configuration register
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[7:0]|pmp[i*4 + 3]cfg|0x00|0xFF|RW|pmp configuration bits|
|[15:8]|pmp[i*4 + 3]cfg|0x00|0xFF|RW|pmp configuration bits|
|[23:16]|pmp[i*4 + 3]cfg|0x00|0xFF|RW|pmp configuration bits|
|[31:24]|pmp[i*4 + 3]cfg|0x00|0xFF|RW|pmp configuration bits|

#### pmpaddr[0-63]
  
---  
**Address** 0x3b0-0x3ef  
**Reset Value**0x20  
**Priviliege mode** M  
**Description** Physical memory protection address register
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|pmpaddr[i]|0x00000000|0xFFFFFFFF|RW|Physical memory protection address register|

#### mcycle
  
---  
**Address** 0xb00  
**Reset Value**0x1e253  
**Priviliege mode** M  
**Description** Counts the number of clock cycles executed from an arbitrary point in time.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mcycle|0x00000000|0xFFFFFFFF|RW|Counts the number of clock cycles executed from an arbitrary point in time.|

#### minstret
  
---  
**Address** 0xb02  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** Counts the number of instructions completed from an arbitrary point in time.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|minstret|0x00000000|0xFFFFFFFF|RW|Counts the number of instructions completed from an arbitrary point in time.|

#### mhpmcounter[3-31]
  
---  
**Address** 0xb03-0xb1f  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mhpmcounter[i]|0x00000000|0xFFFFFFFF|RW|The mhpmcounter is a 64-bit counter. Returns lower 32 bits in RV32I mode.|

#### mcycleh
  
---  
**Address** 0xb80  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** upper 32 bits of mcycle
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mcycleh|0x00000000|0xFFFFFFFF|RW|upper 32 bits of mcycle|

#### minstreth
  
---  
**Address** 0xb82  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** Upper 32 bits of minstret.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|minstreth|0x00000000|0xFFFFFFFF|RW|Upper 32 bits of minstret.|

#### mhpmcounter[3-31]h
  
---  
**Address** 0xb83-0xb9f  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** The mhpmcounterh returns the upper half word in RV32I systems.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mhpmcounter[i]h|0x00000000|0xFFFFFFFF|RW|The mhpmcounterh returns the upper half word in RV32I systems.|

#### mvendorid
  
---  
**Address** 0xf11  
**Reset Value**0xdeadbeef  
**Priviliege mode** M  
**Description** 
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mvendorid|0xdeadbeef|0|RW||

#### marchid
  
---  
**Address** 0xf12  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** MXLEN-bit read-only register encoding the base microarchitecture of the hart.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|marchid|0x0|0|RW|MXLEN-bit read-only register encoding the base microarchitecture of the hart.|

#### mimpid
  
---  
**Address** 0xf13  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** Provides a unique encoding of the version of the processor implementation.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mimpid|0x0|0|RW|Provides a unique encoding of the version of the processor implementation.|

#### mhartid
  
---  
**Address** 0xf14  
**Reset Value**0x0  
**Priviliege mode** M  
**Description** MXLEN-bit read-only register containing the integer ID of the hardware thread running the code.
|Bits|Field name|legal values|Mask|Access|Description|
| :--- | :--- | :--- | :--- | :--- | :--- |
|[31:0]|mhartid|0x0|0|RW|MXLEN-bit read-only register containing the integer ID of the hardware thread running the code.|
