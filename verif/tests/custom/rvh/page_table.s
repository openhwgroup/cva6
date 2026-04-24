.section .page_table, "aw", @progbits

.balign 4096

.globl __satp_lvl3
__satp_lvl3:
.type __satp_lvl3, @object
.size __satp_lvl3, 4096
.space 4096

.globl __satp_lvl2
__satp_lvl2:
.type __satp_lvl2, @object
.size __satp_lvl2, 4096
.space 4096

.globl __satp_lvl1
__satp_lvl1:
.type __satp_lvl1, @object
.size __satp_lvl1, 4096
.space 4096

.balign 4096*4

.globl __hgatp_lvl3
__hgatp_lvl3:
.type __hgatp_lvl3, @object
.size __hgatp_lvl3, 4096*4
.space 4096*4

.globl __hgatp_lvl2
__hgatp_lvl2:
.type __hgatp_lvl2, @object
.size __hgatp_lvl2, 4096
.space 4096

.globl __hgatp_lvl1
__hgatp_lvl1:
.type __hgatp_lvl1, @object
.size __hgatp_lvl1, 4096
.space 4096
