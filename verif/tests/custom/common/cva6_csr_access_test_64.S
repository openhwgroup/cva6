.macro init
.endm
.section .text.init
.globl _start
.option norvc
_start:
	# CSR_DCSR
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 1968, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 1968, x8
	li x8, 0x000000000000a584
	bne x8, x2, csr_fail
	li x8, 0x4d5ec3b200000000
	csrrw x2, 1968, x8
	li x8, 0x0000000000001a52
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 1968, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 1968, x8
	li x8, 0x000000000000a584
	bne x8, x2, csr_fail
	li x8, 0xdadc26d200000000
	csrrs x2, 1968, x8
	li x8, 0x000000000000bfd6
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 1968, x8
	li x8, 0x000000000000bfd6
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 1968, x8
	li x8, 0x0000000000001a52
	bne x8, x2, csr_fail
	li x8, 0x2498478500000000
	csrrc x2, 1968, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1968, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1968, 0b11010
	li x8, 0x0000000000000004
	bne x8, x2, csr_fail
	csrrwi x2, 1968, 0b00000
	li x8, 0x0000000000000012
	bne x8, x2, csr_fail
	csrrsi x2, 1968, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1968, 0b11010
	li x8, 0x0000000000000004
	bne x8, x2, csr_fail
	csrrsi x2, 1968, 0b00000
	li x8, 0x0000000000000016
	bne x8, x2, csr_fail
	csrrci x2, 1968, 0b00101
	li x8, 0x0000000000000016
	bne x8, x2, csr_fail
	csrrci x2, 1968, 0b11010
	li x8, 0x0000000000000012
	bne x8, x2, csr_fail
	csrrci x2, 1968, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_DPC
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 1969, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 1969, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x39422c9800000000
	csrrw x2, 1969, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 1969, x8
	li x8, 0x39422c9800000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 1969, x8
	li x8, 0xbde7adbda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x4cef0c6900000000
	csrrs x2, 1969, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 1969, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 1969, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xfd3f1f2100000000
	csrrc x2, 1969, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1969, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1969, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 1969, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 1969, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1969, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 1969, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1969, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1969, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 1969, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_DSCRATCH0
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 1970, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 1970, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x5c16715300000000
	csrrw x2, 1970, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 1970, x8
	li x8, 0x5c16715300000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 1970, x8
	li x8, 0xfdb7f5f7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x9a278a0a00000000
	csrrs x2, 1970, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 1970, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 1970, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x69238c3000000000
	csrrc x2, 1970, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1970, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1970, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 1970, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 1970, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1970, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 1970, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1970, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1970, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 1970, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_DSCRATCH1
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 1971, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 1971, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x02e7fe1a00000000
	csrrw x2, 1971, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 1971, x8
	li x8, 0x02e7fe1a00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 1971, x8
	li x8, 0xa7e7ffbfa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xe5d137e700000000
	csrrs x2, 1971, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 1971, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 1971, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x5fc1ada400000000
	csrrc x2, 1971, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1971, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1971, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 1971, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 1971, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1971, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 1971, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1971, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1971, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 1971, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SSTATUS
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 256, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 256, x8
	li x8, 0x800000010005a121
	bne x8, x2, csr_fail
	li x8, 0xc16eddc900000000
	csrrw x2, 256, x8
	li x8, 0x0000000200084012
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 256, x8
	li x8, 0x8000000100000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 256, x8
	li x8, 0x800000010005a121
	bne x8, x2, csr_fail
	li x8, 0x5486cc7400000000
	csrrs x2, 256, x8
	li x8, 0x80000003000de133
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 256, x8
	li x8, 0x80000003000de133
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 256, x8
	li x8, 0x0000000200084012
	bne x8, x2, csr_fail
	li x8, 0x97bac69700000000
	csrrc x2, 256, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 256, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 256, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrwi x2, 256, 0b00000
	li x8, 0x0000000000000012
	bne x8, x2, csr_fail
	csrrsi x2, 256, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 256, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrsi x2, 256, 0b00000
	li x8, 0x0000000000000013
	bne x8, x2, csr_fail
	csrrci x2, 256, 0b00101
	li x8, 0x0000000000000013
	bne x8, x2, csr_fail
	csrrci x2, 256, 0b11010
	li x8, 0x0000000000000012
	bne x8, x2, csr_fail
	csrrci x2, 256, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SIE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 260, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 260, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa6b3e21a00000000
	csrrw x2, 260, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 260, x8
	li x8, 0xa6b3e21a00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 260, x8
	li x8, 0xa7b7e7bfa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf7dadce600000000
	csrrs x2, 260, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 260, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 260, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x46ba090700000000
	csrrc x2, 260, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 260, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 260, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 260, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 260, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 260, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 260, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 260, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 260, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 260, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SIP
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 324, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 324, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xb30528ec00000000
	csrrw x2, 324, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 324, x8
	li x8, 0xb30528ec00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 324, x8
	li x8, 0xb7a5adeda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf4b0a7a100000000
	csrrs x2, 324, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 324, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 324, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x12cb2dcb00000000
	csrrc x2, 324, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 324, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 324, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 324, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 324, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 324, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 324, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 324, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 324, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 324, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_STVEC
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 261, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 261, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x1162afb900000000
	csrrw x2, 261, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 261, x8
	li x8, 0x1162afb900000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 261, x8
	li x8, 0xb5e7afbda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x8e86d23f00000000
	csrrs x2, 261, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 261, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 261, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xbc421cc400000000
	csrrc x2, 261, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 261, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 261, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 261, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 261, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 261, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 261, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 261, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 261, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 261, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SCOUNTEREN
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 262, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 262, x8
	li x8, 0x00000000a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xd5083d8e00000000
	csrrw x2, 262, x8
	li x8, 0x000000005a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 262, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 262, x8
	li x8, 0x00000000a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x922cf92d00000000
	csrrs x2, 262, x8
	li x8, 0x00000000ffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 262, x8
	li x8, 0x00000000ffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 262, x8
	li x8, 0x000000005a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xd3d9437200000000
	csrrc x2, 262, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 262, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 262, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 262, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 262, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 262, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 262, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 262, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 262, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 262, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SSCRATCH
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 320, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 320, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x28476cb200000000
	csrrw x2, 320, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 320, x8
	li x8, 0x28476cb200000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 320, x8
	li x8, 0xade7edb7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf7e473f800000000
	csrrs x2, 320, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 320, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 320, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x225f5f2d00000000
	csrrc x2, 320, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 320, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 320, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 320, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 320, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 320, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 320, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 320, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 320, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 320, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SEPC
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 321, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 321, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x10eae9ca00000000
	csrrw x2, 321, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 321, x8
	li x8, 0x10eae9ca00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 321, x8
	li x8, 0xb5efedefa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x29bfeec300000000
	csrrs x2, 321, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 321, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 321, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x57db1bcf00000000
	csrrc x2, 321, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 321, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 321, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 321, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 321, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 321, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 321, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 321, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 321, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 321, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SCAUSE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 322, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 322, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa5ea4b6f00000000
	csrrw x2, 322, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 322, x8
	li x8, 0xa5ea4b6f00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 322, x8
	li x8, 0xa5efefefa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xac57fc4d00000000
	csrrs x2, 322, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 322, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 322, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xd992986500000000
	csrrc x2, 322, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 322, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 322, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 322, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 322, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 322, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 322, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 322, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 322, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 322, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_STVAL
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 323, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 323, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xe13d8fbf00000000
	csrrw x2, 323, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 323, x8
	li x8, 0xe13d8fbf00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 323, x8
	li x8, 0xe5bdafbfa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x813ddd2d00000000
	csrrs x2, 323, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 323, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 323, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x5ba8589200000000
	csrrc x2, 323, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 323, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 323, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 323, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 323, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 323, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 323, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 323, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 323, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 323, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_SATP
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 384, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 384, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x32e2c6d000000000
	csrrw x2, 384, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 384, x8
	li x8, 0x32e2c6d000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 384, x8
	li x8, 0xb7e7e7f5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa97bc65d00000000
	csrrs x2, 384, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 384, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 384, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x37ea95ef00000000
	csrrc x2, 384, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 384, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 384, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 384, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 384, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 384, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 384, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 384, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 384, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 384, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MSTATUS
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 768, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 768, x8
	li x8, 0x800000050025a1a1
	bne x8, x2, csr_fail
	li x8, 0x08d67a3e00000000
	csrrw x2, 768, x8
	li x8, 0x0000000a005a581a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 768, x8
	li x8, 0x0000000e00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 768, x8
	li x8, 0x8000000f0025a1a1
	bne x8, x2, csr_fail
	li x8, 0xbf42b48300000000
	csrrs x2, 768, x8
	li x8, 0x8000000f007ff9bb
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 768, x8
	li x8, 0x8000000f007ff9bb
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 768, x8
	li x8, 0x0000000a005a581a
	bne x8, x2, csr_fail
	li x8, 0x88f18be200000000
	csrrc x2, 768, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 768, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 768, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrwi x2, 768, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 768, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 768, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrsi x2, 768, 0b00000
	li x8, 0x000000000000001b
	bne x8, x2, csr_fail
	csrrci x2, 768, 0b00101
	li x8, 0x000000000000001b
	bne x8, x2, csr_fail
	csrrci x2, 768, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 768, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MISA
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 769, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 769, x8
	li x8, 0x8000000001a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xae6f634100000000
	csrrw x2, 769, x8
	li x8, 0x40000000025a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 769, x8
	li x8, 0x8000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 769, x8
	li x8, 0x8000000001a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xc8885ab600000000
	csrrs x2, 769, x8
	li x8, 0xc000000003ffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 769, x8
	li x8, 0xc000000003ffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 769, x8
	li x8, 0x40000000025a5a5a
	bne x8, x2, csr_fail
	li x8, 0x91c631af00000000
	csrrc x2, 769, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 769, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 769, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 769, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 769, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 769, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 769, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 769, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 769, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 769, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MEDELEG
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 770, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 770, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x9bb07b9100000000
	csrrw x2, 770, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 770, x8
	li x8, 0x9bb07b9100000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 770, x8
	li x8, 0xbfb5ffb5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x72f5108800000000
	csrrs x2, 770, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 770, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 770, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x9a40d93600000000
	csrrc x2, 770, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 770, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 770, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 770, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 770, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 770, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 770, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 770, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 770, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 770, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MIDELEG
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 771, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 771, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xcd382f1d00000000
	csrrw x2, 771, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 771, x8
	li x8, 0xcd382f1d00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 771, x8
	li x8, 0xedbdafbda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x8b1dd15200000000
	csrrs x2, 771, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 771, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 771, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x1fe5449f00000000
	csrrc x2, 771, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 771, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 771, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 771, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 771, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 771, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 771, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 771, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 771, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 771, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MIE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 772, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 772, x8
	li x8, 0x00000000000001a1
	bne x8, x2, csr_fail
	li x8, 0x3dc0f6fd00000000
	csrrw x2, 772, x8
	li x8, 0x0000000000000a1a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 772, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 772, x8
	li x8, 0x00000000000001a1
	bne x8, x2, csr_fail
	li x8, 0x92a6f4b900000000
	csrrs x2, 772, x8
	li x8, 0x0000000000000bbb
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 772, x8
	li x8, 0x0000000000000bbb
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 772, x8
	li x8, 0x0000000000000a1a
	bne x8, x2, csr_fail
	li x8, 0x2dfebe8d00000000
	csrrc x2, 772, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 772, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 772, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrwi x2, 772, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 772, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 772, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrsi x2, 772, 0b00000
	li x8, 0x000000000000001b
	bne x8, x2, csr_fail
	csrrci x2, 772, 0b00101
	li x8, 0x000000000000001b
	bne x8, x2, csr_fail
	csrrci x2, 772, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 772, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MTVEC
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 773, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 773, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x1967e7b000000000
	csrrw x2, 773, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 773, x8
	li x8, 0x1967e7b000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 773, x8
	li x8, 0xbde7e7b5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xc65e47d400000000
	csrrs x2, 773, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 773, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 773, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x555ad4ed00000000
	csrrc x2, 773, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 773, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 773, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 773, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 773, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 773, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 773, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 773, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 773, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 773, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MCOUNTEREN
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 774, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 774, x8
	li x8, 0x00000000a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x14c5404400000000
	csrrw x2, 774, x8
	li x8, 0x000000005a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 774, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 774, x8
	li x8, 0x00000000a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x4dfa458900000000
	csrrs x2, 774, x8
	li x8, 0x00000000ffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 774, x8
	li x8, 0x00000000ffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 774, x8
	li x8, 0x000000005a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xe4147e5e00000000
	csrrc x2, 774, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 774, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 774, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 774, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 774, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 774, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 774, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 774, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 774, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 774, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MSCRATCH
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 832, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 832, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x0e64a61700000000
	csrrw x2, 832, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 832, x8
	li x8, 0x0e64a61700000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 832, x8
	li x8, 0xafe5a7b7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x7ca8ace800000000
	csrrs x2, 832, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 832, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 832, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xef2952e300000000
	csrrc x2, 832, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 832, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 832, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 832, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 832, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 832, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 832, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 832, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 832, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 832, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MEPC
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 833, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 833, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x9e12971b00000000
	csrrw x2, 833, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 833, x8
	li x8, 0x9e12971b00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 833, x8
	li x8, 0xbfb7b7bfa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf514389b00000000
	csrrs x2, 833, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 833, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 833, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x2b202d1900000000
	csrrc x2, 833, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 833, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 833, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 833, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 833, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 833, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 833, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 833, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 833, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 833, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MCAUSE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 834, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 834, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x7db63f5900000000
	csrrw x2, 834, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 834, x8
	li x8, 0x7db63f5900000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 834, x8
	li x8, 0xfdb7bffda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x11c27b5c00000000
	csrrs x2, 834, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 834, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 834, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xe5afe40200000000
	csrrc x2, 834, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 834, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 834, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 834, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 834, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 834, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 834, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 834, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 834, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 834, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MTVAL
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 835, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 835, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x5ebb79d400000000
	csrrw x2, 835, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 835, x8
	li x8, 0x5ebb79d400000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 835, x8
	li x8, 0xffbffdf5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x7ec5c5fd00000000
	csrrs x2, 835, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 835, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 835, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xd270bc0c00000000
	csrrc x2, 835, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 835, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 835, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 835, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 835, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 835, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 835, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 835, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 835, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 835, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MIP
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 836, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 836, x8
	li x8, 0x0000000000000121
	bne x8, x2, csr_fail
	li x8, 0x9f7fdfc300000000
	csrrw x2, 836, x8
	li x8, 0x0000000000000212
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 836, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 836, x8
	li x8, 0x0000000000000121
	bne x8, x2, csr_fail
	li x8, 0xbcb82fc400000000
	csrrs x2, 836, x8
	li x8, 0x0000000000000333
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 836, x8
	li x8, 0x0000000000000333
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 836, x8
	li x8, 0x0000000000000212
	bne x8, x2, csr_fail
	li x8, 0x23cabd3e00000000
	csrrc x2, 836, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 836, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 836, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrwi x2, 836, 0b00000
	li x8, 0x0000000000000012
	bne x8, x2, csr_fail
	csrrsi x2, 836, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 836, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrsi x2, 836, 0b00000
	li x8, 0x0000000000000013
	bne x8, x2, csr_fail
	csrrci x2, 836, 0b00101
	li x8, 0x0000000000000013
	bne x8, x2, csr_fail
	csrrci x2, 836, 0b11010
	li x8, 0x0000000000000012
	bne x8, x2, csr_fail
	csrrci x2, 836, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MVENDORID
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xe1dbc3b600000000
	csrrw x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x8b421efb00000000
	csrrs x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xf636b20900000000
	csrrc x2, 3857, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3857, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3857, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3857, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3857, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3857, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3857, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3857, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3857, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3857, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MARCHID
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0x20a99f2a00000000
	csrrw x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0x1ba648fc00000000
	csrrs x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	li x8, 0x887b030900000000
	csrrc x2, 3858, x8
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrwi x2, 3858, 0b00101
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrwi x2, 3858, 0b11010
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrwi x2, 3858, 0b00000
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrsi x2, 3858, 0b00101
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrsi x2, 3858, 0b11010
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrsi x2, 3858, 0b00000
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrci x2, 3858, 0b00101
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrci x2, 3858, 0b11010
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	csrrci x2, 3858, 0b00000
	li x8, 0x0000000000000003
	bne x8, x2, csr_fail
	# CSR_MIMPID
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x9cc9750100000000
	csrrw x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xd84481b100000000
	csrrs x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x3182b09d00000000
	csrrc x2, 3859, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3859, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3859, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3859, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3859, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3859, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3859, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3859, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3859, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3859, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MHARTID
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x775d905300000000
	csrrw x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x23f0bb3200000000
	csrrs x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x3e594efe00000000
	csrrc x2, 3860, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3860, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3860, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3860, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3860, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3860, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3860, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3860, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3860, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3860, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MCYCLE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2816, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2816, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa0e42def00000000
	csrrw x2, 2816, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2816, x8
	li x8, 0xa0e42def00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2816, x8
	li x8, 0xa5e5adefa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xafc50dc000000000
	csrrs x2, 2816, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2816, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2816, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xf135c37b00000000
	csrrc x2, 2816, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2816, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2816, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2816, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2816, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2816, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2816, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2816, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2816, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2816, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_MINSTRET
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2818, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2818, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x9cf2093c00000000
	csrrw x2, 2818, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2818, x8
	li x8, 0x9cf2093c00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2818, x8
	li x8, 0xbdf7adbda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xd22102e400000000
	csrrs x2, 2818, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2818, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2818, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x85cee42b00000000
	csrrc x2, 2818, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2818, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2818, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2818, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2818, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2818, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2818, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2818, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2818, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2818, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC1
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2819, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2819, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xbaefdace00000000
	csrrw x2, 2819, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2819, x8
	li x8, 0xbaefdace00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2819, x8
	li x8, 0xbfefffefa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xc3945e1700000000
	csrrs x2, 2819, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2819, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2819, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa1ac3d8900000000
	csrrc x2, 2819, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2819, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2819, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2819, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2819, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2819, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2819, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2819, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2819, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2819, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC2
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2820, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2820, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x1d75d81600000000
	csrrw x2, 2820, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2820, x8
	li x8, 0x1d75d81600000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2820, x8
	li x8, 0xbdf5fdb7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x060f115400000000
	csrrs x2, 2820, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2820, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2820, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xb2b602cb00000000
	csrrc x2, 2820, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2820, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2820, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2820, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2820, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2820, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2820, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2820, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2820, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2820, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC3
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2821, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2821, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x698e39dd00000000
	csrrw x2, 2821, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2821, x8
	li x8, 0x698e39dd00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2821, x8
	li x8, 0xedafbdfda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x816400f800000000
	csrrs x2, 2821, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2821, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2821, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x43a192de00000000
	csrrc x2, 2821, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2821, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2821, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2821, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2821, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2821, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2821, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2821, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2821, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2821, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC4
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2822, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2822, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xce0d698500000000
	csrrw x2, 2822, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2822, x8
	li x8, 0xce0d698500000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2822, x8
	li x8, 0xefadeda5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x874e247e00000000
	csrrs x2, 2822, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2822, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2822, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x8eace03900000000
	csrrc x2, 2822, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2822, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2822, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2822, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2822, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2822, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2822, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2822, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2822, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2822, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC5
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2823, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2823, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x9111408000000000
	csrrw x2, 2823, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2823, x8
	li x8, 0x9111408000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2823, x8
	li x8, 0xb5b5e5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x745ebc0300000000
	csrrs x2, 2823, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2823, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2823, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x8a1de30d00000000
	csrrc x2, 2823, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2823, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2823, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2823, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2823, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2823, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2823, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2823, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2823, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2823, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC6
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2824, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2824, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x87a1152600000000
	csrrw x2, 2824, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2824, x8
	li x8, 0x87a1152600000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2824, x8
	li x8, 0xa7a5b5a7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa4f0a8fb00000000
	csrrs x2, 2824, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2824, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2824, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xbaa5423a00000000
	csrrc x2, 2824, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2824, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2824, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2824, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2824, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2824, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2824, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2824, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2824, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2824, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC1_PMES
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 803, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 803, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x4f1036fa00000000
	csrrw x2, 803, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 803, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 803, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0xbc2b3bd200000000
	csrrs x2, 803, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 803, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 803, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0x9ee7260600000000
	csrrc x2, 803, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 803, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 803, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 803, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 803, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 803, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 803, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 803, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 803, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 803, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC2_PMES
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 804, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 804, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x726443bb00000000
	csrrw x2, 804, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 804, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 804, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0xb1f56a7700000000
	csrrs x2, 804, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 804, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 804, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0x55391e9700000000
	csrrc x2, 804, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 804, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 804, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 804, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 804, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 804, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 804, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 804, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 804, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 804, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC3_PMES
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 805, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 805, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x7ca0f89e00000000
	csrrw x2, 805, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 805, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 805, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x38c607d900000000
	csrrs x2, 805, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 805, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 805, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xbf55b5ae00000000
	csrrc x2, 805, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 805, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 805, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 805, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 805, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 805, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 805, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 805, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 805, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 805, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC4_PMES
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 806, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 806, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0xe9964fd600000000
	csrrw x2, 806, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 806, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 806, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0xe48b060300000000
	csrrs x2, 806, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 806, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 806, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xe3a1f16300000000
	csrrc x2, 806, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 806, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 806, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 806, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 806, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 806, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 806, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 806, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 806, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 806, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC5_PMES
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 807, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 807, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x71f0594d00000000
	csrrw x2, 807, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 807, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 807, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x514b4f1100000000
	csrrs x2, 807, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 807, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 807, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0x96d5f5eb00000000
	csrrc x2, 807, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 807, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 807, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 807, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 807, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 807, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 807, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 807, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 807, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 807, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_GPC6_PMES
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 808, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 808, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0xceedcb5500000000
	csrrw x2, 808, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 808, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 808, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x413b7ab800000000
	csrrs x2, 808, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 808, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 808, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xef9e8a7b00000000
	csrrc x2, 808, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 808, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 808, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 808, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 808, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 808, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 808, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 808, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 808, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 808, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_ICACHE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 1984, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 1984, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0xf190fb6900000000
	csrrw x2, 1984, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 1984, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 1984, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0xd7da3f2900000000
	csrrs x2, 1984, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 1984, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 1984, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xee5cf8ae00000000
	csrrc x2, 1984, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1984, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1984, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrwi x2, 1984, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1984, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1984, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrsi x2, 1984, 0b00000
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrci x2, 1984, 0b00101
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrci x2, 1984, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 1984, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_DCACHE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 1985, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 1985, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0x1c68d91500000000
	csrrw x2, 1985, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 1985, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 1985, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0xe982ae6100000000
	csrrs x2, 1985, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 1985, x8
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 1985, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x3dbd1fed00000000
	csrrc x2, 1985, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1985, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1985, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrwi x2, 1985, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1985, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1985, 0b11010
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrsi x2, 1985, 0b00000
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrci x2, 1985, 0b00101
	li x8, 0x0000000000000001
	bne x8, x2, csr_fail
	csrrci x2, 1985, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 1985, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPCFG0
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 928, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 928, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x8b043fda00000000
	csrrw x2, 928, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 928, x8
	li x8, 0x8b043fda00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 928, x8
	li x8, 0xafa5bfffa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x2dc0e34700000000
	csrrs x2, 928, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 928, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 928, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x04aa2b7300000000
	csrrc x2, 928, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 928, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 928, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 928, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 928, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 928, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 928, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 928, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 928, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 928, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPCFG2
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 930, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 930, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xdf417a4a00000000
	csrrw x2, 930, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 930, x8
	li x8, 0xdf417a4a00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 930, x8
	li x8, 0xffe5ffefa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x4253342300000000
	csrrs x2, 930, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 930, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 930, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xc82e8b7800000000
	csrrc x2, 930, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 930, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 930, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 930, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 930, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 930, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 930, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 930, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 930, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 930, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR0
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 944, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 944, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf0d6a74300000000
	csrrw x2, 944, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 944, x8
	li x8, 0xf0d6a74300000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 944, x8
	li x8, 0xf5f7a7e7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xda5c19aa00000000
	csrrs x2, 944, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 944, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 944, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x2bb0431a00000000
	csrrc x2, 944, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 944, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 944, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 944, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 944, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 944, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 944, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 944, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 944, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 944, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR1
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 945, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 945, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x6b6a6c6f00000000
	csrrw x2, 945, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 945, x8
	li x8, 0x6b6a6c6f00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 945, x8
	li x8, 0xefefedefa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x445dfddb00000000
	csrrs x2, 945, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 945, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 945, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xc6ba0b2a00000000
	csrrc x2, 945, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 945, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 945, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 945, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 945, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 945, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 945, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 945, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 945, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 945, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR2
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 946, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 946, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x7812cec300000000
	csrrw x2, 946, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 946, x8
	li x8, 0x7812cec300000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 946, x8
	li x8, 0xfdb7efe7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xb829146e00000000
	csrrs x2, 946, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 946, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 946, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x97f2b76200000000
	csrrc x2, 946, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 946, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 946, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 946, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 946, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 946, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 946, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 946, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 946, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 946, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR3
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 947, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 947, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf25bc7c000000000
	csrrw x2, 947, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 947, x8
	li x8, 0xf25bc7c000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 947, x8
	li x8, 0xf7ffe7e5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xc965dea600000000
	csrrs x2, 947, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 947, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 947, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xe998675200000000
	csrrc x2, 947, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 947, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 947, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 947, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 947, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 947, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 947, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 947, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 947, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 947, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR4
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 948, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 948, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x50d1af6900000000
	csrrw x2, 948, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 948, x8
	li x8, 0x50d1af6900000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 948, x8
	li x8, 0xf5f5afeda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x57b2595900000000
	csrrs x2, 948, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 948, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 948, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x834549b500000000
	csrrc x2, 948, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 948, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 948, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 948, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 948, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 948, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 948, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 948, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 948, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 948, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR5
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 949, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 949, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x2a7916fc00000000
	csrrw x2, 949, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 949, x8
	li x8, 0x2a7916fc00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 949, x8
	li x8, 0xaffdb7fda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x83e8428100000000
	csrrs x2, 949, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 949, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 949, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x9e7537f500000000
	csrrc x2, 949, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 949, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 949, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 949, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 949, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 949, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 949, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 949, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 949, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 949, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR6
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 950, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 950, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa019770a00000000
	csrrw x2, 950, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 950, x8
	li x8, 0xa019770a00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 950, x8
	li x8, 0xa5bdf7afa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xb73ee83e00000000
	csrrs x2, 950, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 950, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 950, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x5f59ad5800000000
	csrrc x2, 950, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 950, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 950, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 950, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 950, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 950, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 950, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 950, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 950, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 950, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR7
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 951, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 951, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x341b018c00000000
	csrrw x2, 951, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 951, x8
	li x8, 0x341b018c00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 951, x8
	li x8, 0xb5bfa5ada5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf0ca8e4500000000
	csrrs x2, 951, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 951, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 951, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x7efbc56700000000
	csrrc x2, 951, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 951, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 951, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 951, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 951, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 951, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 951, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 951, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 951, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 951, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR8
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 952, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 952, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x1d68f5b000000000
	csrrw x2, 952, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 952, x8
	li x8, 0x1d68f5b000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 952, x8
	li x8, 0xbdedf5b5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x6cd7a49d00000000
	csrrs x2, 952, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 952, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 952, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x0b5b0ac200000000
	csrrc x2, 952, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 952, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 952, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 952, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 952, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 952, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 952, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 952, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 952, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 952, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR9
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 953, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 953, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x3f06fb1d00000000
	csrrw x2, 953, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 953, x8
	li x8, 0x3f06fb1d00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 953, x8
	li x8, 0xbfa7ffbda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x478bf3cc00000000
	csrrs x2, 953, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 953, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 953, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x9d08f95300000000
	csrrc x2, 953, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 953, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 953, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 953, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 953, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 953, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 953, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 953, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 953, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 953, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR10
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 954, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 954, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa672433800000000
	csrrw x2, 954, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 954, x8
	li x8, 0xa672433800000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 954, x8
	li x8, 0xa7f7e7bda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xb818918300000000
	csrrs x2, 954, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 954, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 954, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x5090c63b00000000
	csrrc x2, 954, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 954, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 954, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 954, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 954, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 954, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 954, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 954, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 954, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 954, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR11
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 955, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 955, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xbf12713e00000000
	csrrw x2, 955, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 955, x8
	li x8, 0xbf12713e00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 955, x8
	li x8, 0xbfb7f5bfa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x06bba5c300000000
	csrrs x2, 955, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 955, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 955, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x67ebeac400000000
	csrrc x2, 955, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 955, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 955, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 955, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 955, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 955, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 955, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 955, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 955, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 955, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR12
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 956, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 956, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x84a9f27d00000000
	csrrw x2, 956, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 956, x8
	li x8, 0x84a9f27d00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 956, x8
	li x8, 0xa5adf7fda5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xf872a5ea00000000
	csrrs x2, 956, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 956, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 956, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x47cb14e400000000
	csrrc x2, 956, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 956, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 956, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 956, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 956, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 956, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 956, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 956, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 956, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 956, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR13
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 957, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 957, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xa68c906a00000000
	csrrw x2, 957, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 957, x8
	li x8, 0xa68c906a00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 957, x8
	li x8, 0xa7adb5efa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xbb09153100000000
	csrrs x2, 957, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 957, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 957, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x998cad8a00000000
	csrrc x2, 957, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 957, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 957, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 957, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 957, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 957, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 957, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 957, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 957, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 957, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR14
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 958, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 958, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xb94aeeae00000000
	csrrw x2, 958, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 958, x8
	li x8, 0xb94aeeae00000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 958, x8
	li x8, 0xbdefefafa5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0x363a565d00000000
	csrrs x2, 958, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 958, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 958, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x3396cd0a00000000
	csrrc x2, 958, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 958, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 958, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 958, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 958, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 958, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 958, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 958, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 958, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 958, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_PMPADDR15
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 959, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 959, x8
	li x8, 0xa5a5a5a5a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xfddfcf7200000000
	csrrw x2, 959, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 959, x8
	li x8, 0xfddfcf7200000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 959, x8
	li x8, 0xfdffeff7a5a5a5a5
	bne x8, x2, csr_fail
	li x8, 0xcdbde87600000000
	csrrs x2, 959, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 959, x8
	li x8, 0xffffffffffffffff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 959, x8
	li x8, 0x5a5a5a5a5a5a5a5a
	bne x8, x2, csr_fail
	li x8, 0x46b4750f00000000
	csrrc x2, 959, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 959, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 959, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 959, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 959, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 959, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 959, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 959, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 959, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 959, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_FFLAGS
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 1, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 1, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0xe40c213400000000
	csrrw x2, 1, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 1, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 1, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x88d2628300000000
	csrrs x2, 1, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 1, x8
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 1, x8
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	li x8, 0xba2cefdd00000000
	csrrc x2, 1, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 1, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 1, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 1, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 1, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 1, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 1, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 1, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_FRM
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x80391db800000000
	csrrw x2, 2, x8
	li x8, 0x0000000000000002
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2, x8
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	li x8, 0x650e22d800000000
	csrrs x2, 2, x8
	li x8, 0x0000000000000007
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2, x8
	li x8, 0x0000000000000007
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2, x8
	li x8, 0x0000000000000002
	bne x8, x2, csr_fail
	li x8, 0x8e7229c000000000
	csrrc x2, 2, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2, 0b00000
	li x8, 0x0000000000000002
	bne x8, x2, csr_fail
	csrrsi x2, 2, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2, 0b00000
	li x8, 0x0000000000000007
	bne x8, x2, csr_fail
	csrrci x2, 2, 0b00101
	li x8, 0x0000000000000007
	bne x8, x2, csr_fail
	csrrci x2, 2, 0b11010
	li x8, 0x0000000000000002
	bne x8, x2, csr_fail
	csrrci x2, 2, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_FCSR
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 3, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 3, x8
	li x8, 0x00000000000000a5
	bne x8, x2, csr_fail
	li x8, 0xa0aca67100000000
	csrrw x2, 3, x8
	li x8, 0x000000000000005a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 3, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 3, x8
	li x8, 0x00000000000000a5
	bne x8, x2, csr_fail
	li x8, 0xcb1fba7f00000000
	csrrs x2, 3, x8
	li x8, 0x00000000000000ff
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 3, x8
	li x8, 0x00000000000000ff
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 3, x8
	li x8, 0x000000000000005a
	bne x8, x2, csr_fail
	li x8, 0x1a4e8cb300000000
	csrrc x2, 3, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 3, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 3, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 3, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 3, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 3, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 3, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_FTRAN
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 2048, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 2048, x8
	li x8, 0x0000000000000025
	bne x8, x2, csr_fail
	li x8, 0xcb9ab24000000000
	csrrw x2, 2048, x8
	li x8, 0x000000000000005a
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 2048, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 2048, x8
	li x8, 0x0000000000000025
	bne x8, x2, csr_fail
	li x8, 0x0739cab000000000
	csrrs x2, 2048, x8
	li x8, 0x000000000000007f
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 2048, x8
	li x8, 0x000000000000007f
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 2048, x8
	li x8, 0x000000000000005a
	bne x8, x2, csr_fail
	li x8, 0xe2580c7600000000
	csrrc x2, 2048, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2048, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 2048, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrwi x2, 2048, 0b00000
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrsi x2, 2048, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 2048, 0b11010
	li x8, 0x0000000000000005
	bne x8, x2, csr_fail
	csrrsi x2, 2048, 0b00000
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2048, 0b00101
	li x8, 0x000000000000001f
	bne x8, x2, csr_fail
	csrrci x2, 2048, 0b11010
	li x8, 0x000000000000001a
	bne x8, x2, csr_fail
	csrrci x2, 2048, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_CYCLE
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x9f03938c00000000
	csrrw x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x1b2589b700000000
	csrrs x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x1e9235bf00000000
	csrrc x2, 3072, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3072, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3072, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3072, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3072, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3072, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3072, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3072, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3072, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3072, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	# CSR_INSTRET
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrw x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrw x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x8485906a00000000
	csrrw x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrs x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrs x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x936661ee00000000
	csrrs x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa5a5a5a5a5a5a5a5
	csrrc x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0x5a5a5a5a5a5a5a5a
	csrrc x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	li x8, 0xa185710900000000
	csrrc x2, 3074, x8
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3074, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3074, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrwi x2, 3074, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3074, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3074, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrsi x2, 3074, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3074, 0b00101
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3074, 0b11010
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrrci x2, 3074, 0b00000
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail
	csrr x2, 3074
	li x8, 0x0000000000000000
	bne x8, x2, csr_fail


csr_pass:
    li x18, 123456789
    li x17, 0x60000000
    sw x18,0(x17)
    wfi

csr_fail:
    li x18, 1
    li x17, 0x60000000
    sw x18,0(x17)
    wfi
	
