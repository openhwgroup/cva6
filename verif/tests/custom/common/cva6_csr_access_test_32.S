.macro init
.endm
.section .text.init
.globl _start
.option norvc
_start:
	# CSR_DCSR
	li x6, 0xa5a5a5a5
	csrrw x12, 1968, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 1968, x6
	li x6, 0x0000a584
	bne x6, x12, csr_fail
	li x6, 0xf98bef6d
	csrrw x12, 1968, x6
	li x6, 0x00001a52
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 1968, x6
	li x6, 0x0000af44
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 1968, x6
	li x6, 0x0000afc4
	bne x6, x12, csr_fail
	li x6, 0x703ef472
	csrrs x12, 1968, x6
	li x6, 0x0000bfd6
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 1968, x6
	li x6, 0x0000bfd6
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 1968, x6
	li x6, 0x00001a52
	bne x6, x12, csr_fail
	li x6, 0xe1a6b6eb
	csrrc x12, 1968, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1968, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1968, 0b11010
	li x6, 0x00000004
	bne x6, x12, csr_fail
	csrrwi x12, 1968, 0b11000
	li x6, 0x00000012
	bne x6, x12, csr_fail
	csrrsi x12, 1968, 0b00101
	li x6, 0x00000010
	bne x6, x12, csr_fail
	csrrsi x12, 1968, 0b11010
	li x6, 0x00000014
	bne x6, x12, csr_fail
	csrrsi x12, 1968, 0b11101
	li x6, 0x00000016
	bne x6, x12, csr_fail
	csrrci x12, 1968, 0b00101
	li x6, 0x00000016
	bne x6, x12, csr_fail
	csrrci x12, 1968, 0b11010
	li x6, 0x00000012
	bne x6, x12, csr_fail
	csrrci x12, 1968, 0b11000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_DPC
	li x6, 0xa5a5a5a5
	csrrw x12, 1969, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 1969, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xce6fc9c3
	csrrw x12, 1969, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 1969, x6
	li x6, 0xce6fc9c3
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 1969, x6
	li x6, 0xefefede7
	bne x6, x12, csr_fail
	li x6, 0xd2e4b654
	csrrs x12, 1969, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 1969, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 1969, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xde38cc00
	csrrc x12, 1969, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1969, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1969, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 1969, 0b00100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 1969, 0b00101
	li x6, 0x00000004
	bne x6, x12, csr_fail
	csrrsi x12, 1969, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 1969, 0b10101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1969, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1969, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 1969, 0b01101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_DSCRATCH0
	li x6, 0xa5a5a5a5
	csrrw x12, 1970, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 1970, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xb333acc1
	csrrw x12, 1970, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 1970, x6
	li x6, 0xb333acc1
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 1970, x6
	li x6, 0xb7b7ade5
	bne x6, x12, csr_fail
	li x6, 0xa1233498
	csrrs x12, 1970, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 1970, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 1970, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x888d52bc
	csrrc x12, 1970, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1970, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1970, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 1970, 0b10000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 1970, 0b00101
	li x6, 0x00000010
	bne x6, x12, csr_fail
	csrrsi x12, 1970, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 1970, 0b00110
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1970, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1970, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 1970, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_DSCRATCH1
	li x6, 0xa5a5a5a5
	csrrw x12, 1971, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 1971, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xb1a692a8
	csrrw x12, 1971, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 1971, x6
	li x6, 0xb1a692a8
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 1971, x6
	li x6, 0xb5a7b7ad
	bne x6, x12, csr_fail
	li x6, 0x01944b0c
	csrrs x12, 1971, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 1971, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 1971, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xbe30d276
	csrrc x12, 1971, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1971, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1971, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 1971, 0b10000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 1971, 0b00101
	li x6, 0x00000010
	bne x6, x12, csr_fail
	csrrsi x12, 1971, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 1971, 0b01011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1971, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1971, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 1971, 0b10000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SSTATUS
	li x6, 0xa5a5a5a5
	csrrw x12, 256, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 256, x6
	li x6, 0x8005a121
	bne x6, x12, csr_fail
	li x6, 0xc51dc272
	csrrw x12, 256, x6
	li x6, 0x00084012
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 256, x6
	li x6, 0x800dc032
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 256, x6
	li x6, 0x800de133
	bne x6, x12, csr_fail
	li x6, 0x4f5f8ca9
	csrrs x12, 256, x6
	li x6, 0x800de133
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 256, x6
	li x6, 0x800de133
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 256, x6
	li x6, 0x00084012
	bne x6, x12, csr_fail
	li x6, 0x251d0a7d
	csrrc x12, 256, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 256, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 256, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrwi x12, 256, 0b01100
	li x6, 0x00000012
	bne x6, x12, csr_fail
	csrrsi x12, 256, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 256, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrsi x12, 256, 0b01001
	li x6, 0x00000013
	bne x6, x12, csr_fail
	csrrci x12, 256, 0b00101
	li x6, 0x00000013
	bne x6, x12, csr_fail
	csrrci x12, 256, 0b11010
	li x6, 0x00000012
	bne x6, x12, csr_fail
	csrrci x12, 256, 0b00111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SIE
	li x6, 0xa5a5a5a5
	csrrw x12, 260, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 260, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x7e799466
	csrrw x12, 260, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 260, x6
	li x6, 0x7e799466
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 260, x6
	li x6, 0xfffdb5e7
	bne x6, x12, csr_fail
	li x6, 0x0d0a2c4a
	csrrs x12, 260, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 260, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 260, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xfc02e64e
	csrrc x12, 260, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 260, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 260, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 260, 0b11101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 260, 0b00101
	li x6, 0x0000001d
	bne x6, x12, csr_fail
	csrrsi x12, 260, 0b11010
	li x6, 0x0000001d
	bne x6, x12, csr_fail
	csrrsi x12, 260, 0b00100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 260, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 260, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 260, 0b10111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SIP
	li x6, 0xa5a5a5a5
	csrrw x12, 324, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 324, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x150f7660
	csrrw x12, 324, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 324, x6
	li x6, 0x150f7660
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 324, x6
	li x6, 0xb5aff7e5
	bne x6, x12, csr_fail
	li x6, 0xb23ff77b
	csrrs x12, 324, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 324, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 324, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xe94e2de8
	csrrc x12, 324, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 324, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 324, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 324, 0b10101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 324, 0b00101
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 324, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 324, 0b10110
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 324, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 324, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 324, 0b11101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_STVEC
	li x6, 0xa5a5a5a5
	csrrw x12, 261, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 261, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x360c495b
	csrrw x12, 261, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 261, x6
	li x6, 0x360c495b
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 261, x6
	li x6, 0xb7adedff
	bne x6, x12, csr_fail
	li x6, 0xc2abbf8d
	csrrs x12, 261, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 261, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 261, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x7ffb7b05
	csrrc x12, 261, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 261, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 261, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 261, 0b01010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 261, 0b00101
	li x6, 0x0000000a
	bne x6, x12, csr_fail
	csrrsi x12, 261, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 261, 0b11000
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 261, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 261, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 261, 0b00110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SCOUNTEREN
	li x6, 0xa5a5a5a5
	csrrw x12, 262, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 262, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x8d0cf09d
	csrrw x12, 262, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 262, x6
	li x6, 0x8d0cf09d
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 262, x6
	li x6, 0xadadf5bd
	bne x6, x12, csr_fail
	li x6, 0x2d88a314
	csrrs x12, 262, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 262, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 262, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xba9207f2
	csrrc x12, 262, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 262, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 262, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 262, 0b11101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 262, 0b00101
	li x6, 0x0000001d
	bne x6, x12, csr_fail
	csrrsi x12, 262, 0b11010
	li x6, 0x0000001d
	bne x6, x12, csr_fail
	csrrsi x12, 262, 0b11100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 262, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 262, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 262, 0b00011
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SSCRATCH
	li x6, 0xa5a5a5a5
	csrrw x12, 320, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 320, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x67087ba3
	csrrw x12, 320, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 320, x6
	li x6, 0x67087ba3
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 320, x6
	li x6, 0xe7adffa7
	bne x6, x12, csr_fail
	li x6, 0xa1f6b125
	csrrs x12, 320, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 320, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 320, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x9872e7cf
	csrrc x12, 320, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 320, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 320, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 320, 0b00110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 320, 0b00101
	li x6, 0x00000006
	bne x6, x12, csr_fail
	csrrsi x12, 320, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 320, 0b00100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 320, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 320, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 320, 0b10101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SEPC
	li x6, 0xa5a5a5a5
	csrrw x12, 321, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 321, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x6e57e7a7
	csrrw x12, 321, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 321, x6
	li x6, 0x6e57e7a7
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 321, x6
	li x6, 0xeff7e7a7
	bne x6, x12, csr_fail
	li x6, 0xb7a9644a
	csrrs x12, 321, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 321, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 321, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x16d18921
	csrrc x12, 321, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 321, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 321, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 321, 0b10110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 321, 0b00101
	li x6, 0x00000016
	bne x6, x12, csr_fail
	csrrsi x12, 321, 0b11010
	li x6, 0x00000017
	bne x6, x12, csr_fail
	csrrsi x12, 321, 0b00011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 321, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 321, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 321, 0b10010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SCAUSE
	li x6, 0xa5a5a5a5
	csrrw x12, 322, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 322, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x23305176
	csrrw x12, 322, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 322, x6
	li x6, 0x23305176
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 322, x6
	li x6, 0xa7b5f5f7
	bne x6, x12, csr_fail
	li x6, 0x2be07645
	csrrs x12, 322, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 322, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 322, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x4ae3926e
	csrrc x12, 322, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 322, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 322, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 322, 0b10100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 322, 0b00101
	li x6, 0x00000014
	bne x6, x12, csr_fail
	csrrsi x12, 322, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 322, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 322, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 322, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 322, 0b01101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_STVAL
	li x6, 0xa5a5a5a5
	csrrw x12, 323, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 323, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xb75ec6a1
	csrrw x12, 323, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 323, x6
	li x6, 0xb75ec6a1
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 323, x6
	li x6, 0xb7ffe7a5
	bne x6, x12, csr_fail
	li x6, 0xf87ea7d7
	csrrs x12, 323, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 323, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 323, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xfefe4b1f
	csrrc x12, 323, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 323, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 323, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 323, 0b01111
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 323, 0b00101
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 323, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 323, 0b01110
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 323, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 323, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 323, 0b00010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_SATP
	li x6, 0xa5a5a5a5
	csrrw x12, 384, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 384, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x1fc829c6
	csrrw x12, 384, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 384, x6
	li x6, 0x1fc829c6
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 384, x6
	li x6, 0xbfedade7
	bne x6, x12, csr_fail
	li x6, 0xb74e3d9b
	csrrs x12, 384, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 384, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 384, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x2de43e33
	csrrc x12, 384, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 384, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 384, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 384, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 384, 0b00101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 384, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 384, 0b10110
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 384, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 384, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 384, 0b00000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MSTATUS
	li x6, 0xa5a5a5a5
	csrrw x12, 768, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 768, x6
	li x6, 0x8025a1a1
	bne x6, x12, csr_fail
	li x6, 0xd99beb37
	csrrw x12, 768, x6
	li x6, 0x005a581a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 768, x6
	li x6, 0x801be933
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 768, x6
	li x6, 0x803fe9b3
	bne x6, x12, csr_fail
	li x6, 0xbc7df450
	csrrs x12, 768, x6
	li x6, 0x807ff9bb
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 768, x6
	li x6, 0x807ff9bb
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 768, x6
	li x6, 0x005a581a
	bne x6, x12, csr_fail
	li x6, 0x2dcec385
	csrrc x12, 768, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 768, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 768, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrwi x12, 768, 0b10001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 768, 0b00101
	li x6, 0x00000011
	bne x6, x12, csr_fail
	csrrsi x12, 768, 0b11010
	li x6, 0x00000011
	bne x6, x12, csr_fail
	csrrsi x12, 768, 0b10001
	li x6, 0x0000001b
	bne x6, x12, csr_fail
	csrrci x12, 768, 0b00101
	li x6, 0x0000001b
	bne x6, x12, csr_fail
	csrrci x12, 768, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 768, 0b10111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MISA
	li x6, 0xa5a5a5a5
	csrrw x12, 769, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 769, x6
	li x6, 0x81a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xc6f9f09d
	csrrw x12, 769, x6
	li x6, 0x425a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 769, x6
	li x6, 0xc2f9f09d
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 769, x6
	li x6, 0xc3fdf5bd
	bne x6, x12, csr_fail
	li x6, 0x941944c6
	csrrs x12, 769, x6
	li x6, 0xc3ffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 769, x6
	li x6, 0xc3ffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 769, x6
	li x6, 0x425a5a5a
	bne x6, x12, csr_fail
	li x6, 0x549e01a8
	csrrc x12, 769, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 769, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 769, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 769, 0b01100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 769, 0b00101
	li x6, 0x0000000c
	bne x6, x12, csr_fail
	csrrsi x12, 769, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 769, 0b11100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 769, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 769, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 769, 0b00000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MEDELEG
	li x6, 0xa5a5a5a5
	csrrw x12, 770, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 770, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xd4223b1a
	csrrw x12, 770, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 770, x6
	li x6, 0xd4223b1a
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 770, x6
	li x6, 0xf5a7bfbf
	bne x6, x12, csr_fail
	li x6, 0x8ee01d65
	csrrs x12, 770, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 770, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 770, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xaa8788b6
	csrrc x12, 770, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 770, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 770, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 770, 0b00101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 770, 0b00101
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 770, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 770, 0b10100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 770, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 770, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 770, 0b10001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MIDELEG
	li x6, 0xa5a5a5a5
	csrrw x12, 771, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 771, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x4c15bb8d
	csrrw x12, 771, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 771, x6
	li x6, 0x4c15bb8d
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 771, x6
	li x6, 0xedb5bfad
	bne x6, x12, csr_fail
	li x6, 0xb2a095a2
	csrrs x12, 771, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 771, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 771, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x45e27139
	csrrc x12, 771, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 771, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 771, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 771, 0b00001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 771, 0b00101
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrsi x12, 771, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 771, 0b01010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 771, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 771, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 771, 0b10001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MIE
	li x6, 0xa5a5a5a5
	csrrw x12, 772, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 772, x6
	li x6, 0x000001a1
	bne x6, x12, csr_fail
	li x6, 0x162ef63a
	csrrw x12, 772, x6
	li x6, 0x00000a1a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 772, x6
	li x6, 0x0000023a
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 772, x6
	li x6, 0x000003bb
	bne x6, x12, csr_fail
	li x6, 0x6c5fb732
	csrrs x12, 772, x6
	li x6, 0x00000bbb
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 772, x6
	li x6, 0x00000bbb
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 772, x6
	li x6, 0x00000a1a
	bne x6, x12, csr_fail
	li x6, 0xe60ac531
	csrrc x12, 772, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 772, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 772, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrwi x12, 772, 0b01100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 772, 0b00101
	li x6, 0x00000008
	bne x6, x12, csr_fail
	csrrsi x12, 772, 0b11010
	li x6, 0x00000009
	bne x6, x12, csr_fail
	csrrsi x12, 772, 0b00010
	li x6, 0x0000001b
	bne x6, x12, csr_fail
	csrrci x12, 772, 0b00101
	li x6, 0x0000001b
	bne x6, x12, csr_fail
	csrrci x12, 772, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 772, 0b01100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MTVEC
	li x6, 0xa5a5a5a5
	csrrw x12, 773, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 773, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x8667081c
	csrrw x12, 773, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 773, x6
	li x6, 0x8667081c
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 773, x6
	li x6, 0xa7e7adbd
	bne x6, x12, csr_fail
	li x6, 0x043d9536
	csrrs x12, 773, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 773, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 773, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x31d552e8
	csrrc x12, 773, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 773, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 773, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 773, 0b00011
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 773, 0b00101
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrsi x12, 773, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 773, 0b11000
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 773, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 773, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 773, 0b00000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MCOUNTEREN
	li x6, 0xa5a5a5a5
	csrrw x12, 774, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 774, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x74af0220
	csrrw x12, 774, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 774, x6
	li x6, 0x74af0220
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 774, x6
	li x6, 0xf5afa7a5
	bne x6, x12, csr_fail
	li x6, 0x03fbb4a8
	csrrs x12, 774, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 774, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 774, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x3df8f82e
	csrrc x12, 774, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 774, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 774, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 774, 0b11011
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 774, 0b00101
	li x6, 0x0000001b
	bne x6, x12, csr_fail
	csrrsi x12, 774, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 774, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 774, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 774, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 774, 0b00010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MSCRATCH
	li x6, 0xa5a5a5a5
	csrrw x12, 832, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 832, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x130859c9
	csrrw x12, 832, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 832, x6
	li x6, 0x130859c9
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 832, x6
	li x6, 0xb7adfded
	bne x6, x12, csr_fail
	li x6, 0x4821c2b9
	csrrs x12, 832, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 832, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 832, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x29c2a6d3
	csrrc x12, 832, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 832, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 832, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 832, 0b01010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 832, 0b00101
	li x6, 0x0000000a
	bne x6, x12, csr_fail
	csrrsi x12, 832, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 832, 0b10001
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 832, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 832, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 832, 0b11101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MEPC
	li x6, 0xa5a5a5a5
	csrrw x12, 833, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 833, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xfc5e0c24
	csrrw x12, 833, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 833, x6
	li x6, 0xfc5e0c24
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 833, x6
	li x6, 0xfdffada5
	bne x6, x12, csr_fail
	li x6, 0xb15c3cf9
	csrrs x12, 833, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 833, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 833, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xc74349c5
	csrrc x12, 833, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 833, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 833, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 833, 0b10001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 833, 0b00101
	li x6, 0x00000011
	bne x6, x12, csr_fail
	csrrsi x12, 833, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 833, 0b01001
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 833, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 833, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 833, 0b00010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MCAUSE
	li x6, 0xa5a5a5a5
	csrrw x12, 834, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 834, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x9a9f401d
	csrrw x12, 834, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 834, x6
	li x6, 0x9a9f401d
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 834, x6
	li x6, 0xbfbfe5bd
	bne x6, x12, csr_fail
	li x6, 0xd3f532ca
	csrrs x12, 834, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 834, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 834, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xf266aa31
	csrrc x12, 834, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 834, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 834, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 834, 0b01111
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 834, 0b00101
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 834, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 834, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 834, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 834, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 834, 0b10111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MTVAL
	li x6, 0xa5a5a5a5
	csrrw x12, 835, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 835, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x473b8d42
	csrrw x12, 835, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 835, x6
	li x6, 0x473b8d42
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 835, x6
	li x6, 0xe7bfade7
	bne x6, x12, csr_fail
	li x6, 0x96d3322a
	csrrs x12, 835, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 835, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 835, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x3ab5e9f0
	csrrc x12, 835, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 835, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 835, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 835, 0b11111
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 835, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 835, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 835, 0b01001
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 835, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 835, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 835, 0b00001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MIP
	li x6, 0xa5a5a5a5
	csrrw x12, 836, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 836, x6
	li x6, 0x00000121
	bne x6, x12, csr_fail
	li x6, 0x173cc177
	csrrw x12, 836, x6
	li x6, 0x00000212
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 836, x6
	li x6, 0x00000133
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 836, x6
	li x6, 0x00000133
	bne x6, x12, csr_fail
	li x6, 0xdaa90bd0
	csrrs x12, 836, x6
	li x6, 0x00000333
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 836, x6
	li x6, 0x00000333
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 836, x6
	li x6, 0x00000212
	bne x6, x12, csr_fail
	li x6, 0x602b8a98
	csrrc x12, 836, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 836, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 836, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrwi x12, 836, 0b11101
	li x6, 0x00000012
	bne x6, x12, csr_fail
	csrrsi x12, 836, 0b00101
	li x6, 0x00000011
	bne x6, x12, csr_fail
	csrrsi x12, 836, 0b11010
	li x6, 0x00000011
	bne x6, x12, csr_fail
	csrrsi x12, 836, 0b11110
	li x6, 0x00000013
	bne x6, x12, csr_fail
	csrrci x12, 836, 0b00101
	li x6, 0x00000013
	bne x6, x12, csr_fail
	csrrci x12, 836, 0b11010
	li x6, 0x00000012
	bne x6, x12, csr_fail
	csrrci x12, 836, 0b01110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MVENDORID
	li x6, 0xa5a5a5a5
	csrrw x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x58980db4
	csrrw x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x7b9c4992
	csrrs x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa8ae1dce
	csrrc x12, 3857, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3857, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3857, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3857, 0b01000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3857, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3857, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3857, 0b01101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3857, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3857, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3857, 0b11001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MARCHID
	li x6, 0xa5a5a5a5
	csrrw x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0x26a47a6b
	csrrw x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0x50ab9e88
	csrrs x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0xe02f62d0
	csrrc x12, 3858, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrwi x12, 3858, 0b00101
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrwi x12, 3858, 0b11010
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrwi x12, 3858, 0b01010
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrsi x12, 3858, 0b00101
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrsi x12, 3858, 0b11010
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrsi x12, 3858, 0b01010
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrci x12, 3858, 0b00101
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrci x12, 3858, 0b11010
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrci x12, 3858, 0b00000
	li x6, 0x00000003
	bne x6, x12, csr_fail
	# CSR_MIMPID
	li x6, 0xa5a5a5a5
	csrrw x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xaa338040
	csrrw x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xbc407b85
	csrrs x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xfe84b59d
	csrrc x12, 3859, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3859, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3859, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3859, 0b01111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3859, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3859, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3859, 0b10011
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3859, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3859, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3859, 0b01000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MHARTID
	li x6, 0xa5a5a5a5
	csrrw x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x7920b2bb
	csrrw x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xf0e7a5dd
	csrrs x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x467b7f27
	csrrc x12, 3860, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3860, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3860, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3860, 0b01101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3860, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3860, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3860, 0b00111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3860, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3860, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3860, 0b00000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MCYCLE
	li x6, 0xa5a5a5a5
	csrrw x12, 2816, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2816, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x92fe9536
	csrrw x12, 2816, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2816, x6
	li x6, 0x92fe9536
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2816, x6
	li x6, 0xb7ffb5b7
	bne x6, x12, csr_fail
	li x6, 0x0702a58a
	csrrs x12, 2816, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2816, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2816, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa580e679
	csrrc x12, 2816, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2816, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2816, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2816, 0b00010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2816, 0b00101
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrsi x12, 2816, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 2816, 0b01011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2816, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2816, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2816, 0b01001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MCYCLE_H
	li x6, 0xa5a5a5a5
	csrrw x12, 2944, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2944, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x2a573677
	csrrw x12, 2944, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2944, x6
	li x6, 0x2a573677
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2944, x6
	li x6, 0xaff7b7f7
	bne x6, x12, csr_fail
	li x6, 0x6091ef93
	csrrs x12, 2944, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2944, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2944, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x9cd2fd96
	csrrc x12, 2944, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2944, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2944, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2944, 0b01100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2944, 0b00101
	li x6, 0x0000000c
	bne x6, x12, csr_fail
	csrrsi x12, 2944, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 2944, 0b10010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2944, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2944, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2944, 0b01101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MINSTRET
	li x6, 0xa5a5a5a5
	csrrw x12, 2818, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2818, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xb6989928
	csrrw x12, 2818, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2818, x6
	li x6, 0xb6989928
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2818, x6
	li x6, 0xb7bdbdad
	bne x6, x12, csr_fail
	li x6, 0xe10009d9
	csrrs x12, 2818, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2818, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2818, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x4a7dcaa2
	csrrc x12, 2818, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2818, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2818, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2818, 0b01001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2818, 0b00101
	li x6, 0x00000009
	bne x6, x12, csr_fail
	csrrsi x12, 2818, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 2818, 0b01111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2818, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2818, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2818, 0b11111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_MINSTRET_H
	li x6, 0xa5a5a5a5
	csrrw x12, 2946, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2946, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xa1436b7d
	csrrw x12, 2946, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2946, x6
	li x6, 0xa1436b7d
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2946, x6
	li x6, 0xa5e7effd
	bne x6, x12, csr_fail
	li x6, 0x88d4434a
	csrrs x12, 2946, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2946, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2946, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x7f48f878
	csrrc x12, 2946, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2946, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2946, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2946, 0b10101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2946, 0b00101
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 2946, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 2946, 0b10100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2946, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2946, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2946, 0b10000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC1
	li x6, 0xa5a5a5a5
	csrrw x12, 2819, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2819, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xf29a78cc
	csrrw x12, 2819, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2819, x6
	li x6, 0xf29a78cc
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2819, x6
	li x6, 0xf7bffded
	bne x6, x12, csr_fail
	li x6, 0xad9fd44b
	csrrs x12, 2819, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2819, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2819, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x768bed2b
	csrrc x12, 2819, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2819, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2819, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2819, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2819, 0b00101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2819, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 2819, 0b01100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2819, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2819, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2819, 0b01101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC1H
	li x6, 0xa5a5a5a5
	csrrw x12, 2947, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2947, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xbebb8424
	csrrw x12, 2947, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2947, x6
	li x6, 0xbebb8424
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2947, x6
	li x6, 0xbfbfa5a5
	bne x6, x12, csr_fail
	li x6, 0x45577ba1
	csrrs x12, 2947, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2947, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2947, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xd268996a
	csrrc x12, 2947, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2947, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2947, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2947, 0b00100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2947, 0b00101
	li x6, 0x00000004
	bne x6, x12, csr_fail
	csrrsi x12, 2947, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 2947, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2947, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2947, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2947, 0b00100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC2
	li x6, 0xa5a5a5a5
	csrrw x12, 2820, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2820, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xcafd0058
	csrrw x12, 2820, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2820, x6
	li x6, 0xcafd0058
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2820, x6
	li x6, 0xeffda5fd
	bne x6, x12, csr_fail
	li x6, 0x55c517ca
	csrrs x12, 2820, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2820, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2820, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xde971dd4
	csrrc x12, 2820, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2820, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2820, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2820, 0b10101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2820, 0b00101
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 2820, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 2820, 0b00011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2820, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2820, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2820, 0b10100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC2H
	li x6, 0xa5a5a5a5
	csrrw x12, 2948, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2948, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xe564801e
	csrrw x12, 2948, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2948, x6
	li x6, 0xe564801e
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2948, x6
	li x6, 0xe5e5a5bf
	bne x6, x12, csr_fail
	li x6, 0x9a6181e9
	csrrs x12, 2948, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2948, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2948, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xfebbdf95
	csrrc x12, 2948, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2948, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2948, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2948, 0b10001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2948, 0b00101
	li x6, 0x00000011
	bne x6, x12, csr_fail
	csrrsi x12, 2948, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 2948, 0b11000
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2948, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2948, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2948, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC3
	li x6, 0xa5a5a5a5
	csrrw x12, 2821, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2821, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x30d793cb
	csrrw x12, 2821, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2821, x6
	li x6, 0x30d793cb
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2821, x6
	li x6, 0xb5f7b7ef
	bne x6, x12, csr_fail
	li x6, 0xf052838b
	csrrs x12, 2821, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2821, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2821, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x86d5de86
	csrrc x12, 2821, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2821, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2821, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2821, 0b00110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2821, 0b00101
	li x6, 0x00000006
	bne x6, x12, csr_fail
	csrrsi x12, 2821, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 2821, 0b10101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2821, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2821, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2821, 0b10110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC3H
	li x6, 0xa5a5a5a5
	csrrw x12, 2949, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2949, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xeeb16977
	csrrw x12, 2949, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2949, x6
	li x6, 0xeeb16977
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2949, x6
	li x6, 0xefb5edf7
	bne x6, x12, csr_fail
	li x6, 0xabfd710b
	csrrs x12, 2949, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2949, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2949, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa08eb33b
	csrrc x12, 2949, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2949, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2949, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2949, 0b01100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2949, 0b00101
	li x6, 0x0000000c
	bne x6, x12, csr_fail
	csrrsi x12, 2949, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 2949, 0b01010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2949, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2949, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2949, 0b00000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC4
	li x6, 0xa5a5a5a5
	csrrw x12, 2822, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2822, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x35680239
	csrrw x12, 2822, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2822, x6
	li x6, 0x35680239
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2822, x6
	li x6, 0xb5eda7bd
	bne x6, x12, csr_fail
	li x6, 0x05561d07
	csrrs x12, 2822, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2822, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2822, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x944ebe73
	csrrc x12, 2822, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2822, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2822, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2822, 0b00110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2822, 0b00101
	li x6, 0x00000006
	bne x6, x12, csr_fail
	csrrsi x12, 2822, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 2822, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2822, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2822, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2822, 0b10110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC4H
	li x6, 0xa5a5a5a5
	csrrw x12, 2950, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2950, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x2ae4e6d8
	csrrw x12, 2950, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2950, x6
	li x6, 0x2ae4e6d8
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2950, x6
	li x6, 0xafe5e7fd
	bne x6, x12, csr_fail
	li x6, 0xe921f6e1
	csrrs x12, 2950, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2950, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2950, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x19c45173
	csrrc x12, 2950, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2950, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2950, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2950, 0b01110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2950, 0b00101
	li x6, 0x0000000e
	bne x6, x12, csr_fail
	csrrsi x12, 2950, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 2950, 0b11001
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2950, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2950, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2950, 0b01110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC5
	li x6, 0xa5a5a5a5
	csrrw x12, 2823, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2823, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x837e3a6e
	csrrw x12, 2823, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2823, x6
	li x6, 0x837e3a6e
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2823, x6
	li x6, 0xa7ffbfef
	bne x6, x12, csr_fail
	li x6, 0x4411e22c
	csrrs x12, 2823, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2823, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2823, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xc287ebe5
	csrrc x12, 2823, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2823, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2823, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2823, 0b10011
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2823, 0b00101
	li x6, 0x00000013
	bne x6, x12, csr_fail
	csrrsi x12, 2823, 0b11010
	li x6, 0x00000017
	bne x6, x12, csr_fail
	csrrsi x12, 2823, 0b01101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2823, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2823, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2823, 0b01111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC5H
	li x6, 0xa5a5a5a5
	csrrw x12, 2951, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2951, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x07536bcf
	csrrw x12, 2951, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2951, x6
	li x6, 0x07536bcf
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2951, x6
	li x6, 0xa7f7efef
	bne x6, x12, csr_fail
	li x6, 0x4adeb942
	csrrs x12, 2951, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2951, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2951, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x60f1fb98
	csrrc x12, 2951, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2951, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2951, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2951, 0b00000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2951, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 2951, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 2951, 0b01011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2951, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2951, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2951, 0b10111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC6
	li x6, 0xa5a5a5a5
	csrrw x12, 2824, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2824, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x55bb10bb
	csrrw x12, 2824, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2824, x6
	li x6, 0x55bb10bb
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2824, x6
	li x6, 0xf5bfb5bf
	bne x6, x12, csr_fail
	li x6, 0x3ce4dbfe
	csrrs x12, 2824, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2824, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2824, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x4c7a4413
	csrrc x12, 2824, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2824, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2824, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2824, 0b01110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2824, 0b00101
	li x6, 0x0000000e
	bne x6, x12, csr_fail
	csrrsi x12, 2824, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 2824, 0b00000
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2824, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2824, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2824, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC6H
	li x6, 0xa5a5a5a5
	csrrw x12, 2952, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2952, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xf37a6300
	csrrw x12, 2952, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2952, x6
	li x6, 0xf37a6300
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2952, x6
	li x6, 0xf7ffe7a5
	bne x6, x12, csr_fail
	li x6, 0xf152af0a
	csrrs x12, 2952, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2952, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2952, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x3538af66
	csrrc x12, 2952, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2952, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2952, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2952, 0b00110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2952, 0b00101
	li x6, 0x00000006
	bne x6, x12, csr_fail
	csrrsi x12, 2952, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 2952, 0b10101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2952, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2952, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2952, 0b01010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC1_PMES
	li x6, 0xa5a5a5a5
	csrrw x12, 803, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 803, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0xe41f2cdf
	csrrw x12, 803, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 803, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 803, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xb0156aed
	csrrs x12, 803, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 803, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 803, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xc2f3a49c
	csrrc x12, 803, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 803, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 803, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 803, 0b01110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 803, 0b00101
	li x6, 0x0000000e
	bne x6, x12, csr_fail
	csrrsi x12, 803, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 803, 0b01111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 803, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 803, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 803, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC2_PMES
	li x6, 0xa5a5a5a5
	csrrw x12, 804, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 804, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x93627ff8
	csrrw x12, 804, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 804, x6
	li x6, 0x00000018
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 804, x6
	li x6, 0x0000001d
	bne x6, x12, csr_fail
	li x6, 0xaa624a7f
	csrrs x12, 804, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 804, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 804, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xf540269b
	csrrc x12, 804, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 804, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 804, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 804, 0b01000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 804, 0b00101
	li x6, 0x00000008
	bne x6, x12, csr_fail
	csrrsi x12, 804, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 804, 0b11111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 804, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 804, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 804, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC3_PMES
	li x6, 0xa5a5a5a5
	csrrw x12, 805, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 805, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x2724e603
	csrrw x12, 805, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 805, x6
	li x6, 0x00000003
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 805, x6
	li x6, 0x00000007
	bne x6, x12, csr_fail
	li x6, 0x777c5f33
	csrrs x12, 805, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 805, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 805, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0x586b1083
	csrrc x12, 805, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 805, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 805, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 805, 0b11111
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 805, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 805, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 805, 0b01010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 805, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 805, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 805, 0b10101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC4_PMES
	li x6, 0xa5a5a5a5
	csrrw x12, 806, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 806, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0xc097a7a0
	csrrw x12, 806, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 806, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 806, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0xe4073cd5
	csrrs x12, 806, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 806, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 806, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0x57bb5b68
	csrrc x12, 806, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 806, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 806, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 806, 0b01001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 806, 0b00101
	li x6, 0x00000009
	bne x6, x12, csr_fail
	csrrsi x12, 806, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 806, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 806, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 806, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 806, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC5_PMES
	li x6, 0xa5a5a5a5
	csrrw x12, 807, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 807, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x1fc7025a
	csrrw x12, 807, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 807, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 807, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xebe5fccd
	csrrs x12, 807, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 807, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 807, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0x20e31632
	csrrc x12, 807, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 807, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 807, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 807, 0b01010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 807, 0b00101
	li x6, 0x0000000a
	bne x6, x12, csr_fail
	csrrsi x12, 807, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 807, 0b01111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 807, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 807, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 807, 0b01011
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_GPC6_PMES
	li x6, 0xa5a5a5a5
	csrrw x12, 808, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 808, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x64dcfeb7
	csrrw x12, 808, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 808, x6
	li x6, 0x00000017
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 808, x6
	li x6, 0x00000017
	bne x6, x12, csr_fail
	li x6, 0x68881579
	csrrs x12, 808, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 808, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 808, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0x4578638d
	csrrc x12, 808, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 808, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 808, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 808, 0b00010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 808, 0b00101
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrsi x12, 808, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 808, 0b01110
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 808, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 808, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 808, 0b01110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_ICACHE
	li x6, 0xa5a5a5a5
	csrrw x12, 1984, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 1984, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0x53ab47b8
	csrrw x12, 1984, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 1984, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 1984, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0xbc84fe83
	csrrs x12, 1984, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 1984, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 1984, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x12adc901
	csrrc x12, 1984, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1984, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1984, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrwi x12, 1984, 0b01101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 1984, 0b00101
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrsi x12, 1984, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrsi x12, 1984, 0b01000
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrci x12, 1984, 0b00101
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrci x12, 1984, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 1984, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_DCACHE
	li x6, 0xa5a5a5a5
	csrrw x12, 1985, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 1985, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0x3a1d6896
	csrrw x12, 1985, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 1985, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 1985, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0x3bc382a6
	csrrs x12, 1985, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 1985, x6
	li x6, 0x00000001
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 1985, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x643bcc02
	csrrc x12, 1985, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1985, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1985, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrwi x12, 1985, 0b11100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 1985, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 1985, 0b11010
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrsi x12, 1985, 0b10100
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrci x12, 1985, 0b00101
	li x6, 0x00000001
	bne x6, x12, csr_fail
	csrrci x12, 1985, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 1985, 0b10101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPCFG0
	li x6, 0xa5a5a5a5
	csrrw x12, 928, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 928, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x2b4250fc
	csrrw x12, 928, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 928, x6
	li x6, 0x2b4250fc
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 928, x6
	li x6, 0xafe7f5fd
	bne x6, x12, csr_fail
	li x6, 0x81c8bf1c
	csrrs x12, 928, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 928, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 928, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xdd640568
	csrrc x12, 928, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 928, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 928, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 928, 0b00000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 928, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 928, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 928, 0b01111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 928, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 928, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 928, 0b00111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPCFG1
	li x6, 0xa5a5a5a5
	csrrw x12, 929, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 929, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xee2ea5cd
	csrrw x12, 929, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 929, x6
	li x6, 0xee2ea5cd
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 929, x6
	li x6, 0xefafa5ed
	bne x6, x12, csr_fail
	li x6, 0x473fb54e
	csrrs x12, 929, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 929, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 929, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xacd1083c
	csrrc x12, 929, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 929, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 929, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 929, 0b10000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 929, 0b00101
	li x6, 0x00000010
	bne x6, x12, csr_fail
	csrrsi x12, 929, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 929, 0b01100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 929, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 929, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 929, 0b10010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPCFG2
	li x6, 0xa5a5a5a5
	csrrw x12, 930, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 930, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xd82f01cf
	csrrw x12, 930, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 930, x6
	li x6, 0xd82f01cf
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 930, x6
	li x6, 0xfdafa5ef
	bne x6, x12, csr_fail
	li x6, 0x09cd46c4
	csrrs x12, 930, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 930, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 930, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x901fd011
	csrrc x12, 930, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 930, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 930, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 930, 0b00110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 930, 0b00101
	li x6, 0x00000006
	bne x6, x12, csr_fail
	csrrsi x12, 930, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 930, 0b00011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 930, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 930, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 930, 0b11011
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPCFG3
	li x6, 0xa5a5a5a5
	csrrw x12, 931, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 931, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xe12c5746
	csrrw x12, 931, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 931, x6
	li x6, 0xe12c5746
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 931, x6
	li x6, 0xe5adf7e7
	bne x6, x12, csr_fail
	li x6, 0xc61666ef
	csrrs x12, 931, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 931, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 931, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x574b39bc
	csrrc x12, 931, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 931, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 931, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 931, 0b00100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 931, 0b00101
	li x6, 0x00000004
	bne x6, x12, csr_fail
	csrrsi x12, 931, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 931, 0b01111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 931, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 931, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 931, 0b10010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR0
	li x6, 0xa5a5a5a5
	csrrw x12, 944, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 944, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xceb9cc9f
	csrrw x12, 944, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 944, x6
	li x6, 0xceb9cc9f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 944, x6
	li x6, 0xefbdedbf
	bne x6, x12, csr_fail
	li x6, 0x30c1e578
	csrrs x12, 944, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 944, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 944, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xd80ce680
	csrrc x12, 944, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 944, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 944, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 944, 0b00010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 944, 0b00101
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrsi x12, 944, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 944, 0b01100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 944, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 944, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 944, 0b10100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR1
	li x6, 0xa5a5a5a5
	csrrw x12, 945, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 945, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xb193e032
	csrrw x12, 945, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 945, x6
	li x6, 0xb193e032
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 945, x6
	li x6, 0xb5b7e5b7
	bne x6, x12, csr_fail
	li x6, 0x0839e351
	csrrs x12, 945, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 945, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 945, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x425ecc7e
	csrrc x12, 945, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 945, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 945, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 945, 0b10000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 945, 0b00101
	li x6, 0x00000010
	bne x6, x12, csr_fail
	csrrsi x12, 945, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 945, 0b10100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 945, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 945, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 945, 0b01110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR2
	li x6, 0xa5a5a5a5
	csrrw x12, 946, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 946, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xe6893365
	csrrw x12, 946, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 946, x6
	li x6, 0xe6893365
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 946, x6
	li x6, 0xe7adb7e5
	bne x6, x12, csr_fail
	li x6, 0xce9f3535
	csrrs x12, 946, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 946, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 946, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xda0be795
	csrrc x12, 946, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 946, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 946, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 946, 0b11111
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 946, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 946, 0b11010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrsi x12, 946, 0b01010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 946, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 946, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 946, 0b10110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR3
	li x6, 0xa5a5a5a5
	csrrw x12, 947, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 947, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x202f84b4
	csrrw x12, 947, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 947, x6
	li x6, 0x202f84b4
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 947, x6
	li x6, 0xa5afa5b5
	bne x6, x12, csr_fail
	li x6, 0x743f15fb
	csrrs x12, 947, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 947, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 947, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xd9511b1b
	csrrc x12, 947, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 947, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 947, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 947, 0b01010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 947, 0b00101
	li x6, 0x0000000a
	bne x6, x12, csr_fail
	csrrsi x12, 947, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 947, 0b11011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 947, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 947, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 947, 0b00001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR4
	li x6, 0xa5a5a5a5
	csrrw x12, 948, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 948, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x8c7f9c4d
	csrrw x12, 948, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 948, x6
	li x6, 0x8c7f9c4d
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 948, x6
	li x6, 0xadffbded
	bne x6, x12, csr_fail
	li x6, 0x7b56288d
	csrrs x12, 948, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 948, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 948, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x13d22f88
	csrrc x12, 948, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 948, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 948, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 948, 0b00110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 948, 0b00101
	li x6, 0x00000006
	bne x6, x12, csr_fail
	csrrsi x12, 948, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 948, 0b01011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 948, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 948, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 948, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR5
	li x6, 0xa5a5a5a5
	csrrw x12, 949, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 949, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xe27a01ab
	csrrw x12, 949, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 949, x6
	li x6, 0xe27a01ab
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 949, x6
	li x6, 0xe7ffa5af
	bne x6, x12, csr_fail
	li x6, 0x920020c3
	csrrs x12, 949, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 949, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 949, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xf9b95a15
	csrrc x12, 949, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 949, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 949, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 949, 0b00111
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 949, 0b00101
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 949, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 949, 0b00111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 949, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 949, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 949, 0b00010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR6
	li x6, 0xa5a5a5a5
	csrrw x12, 950, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 950, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xafb17ed4
	csrrw x12, 950, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 950, x6
	li x6, 0xafb17ed4
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 950, x6
	li x6, 0xafb5fff5
	bne x6, x12, csr_fail
	li x6, 0x23ba0067
	csrrs x12, 950, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 950, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 950, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xd5a5a621
	csrrc x12, 950, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 950, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 950, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 950, 0b11100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 950, 0b00101
	li x6, 0x0000001c
	bne x6, x12, csr_fail
	csrrsi x12, 950, 0b11010
	li x6, 0x0000001d
	bne x6, x12, csr_fail
	csrrsi x12, 950, 0b01111
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 950, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 950, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 950, 0b01010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR7
	li x6, 0xa5a5a5a5
	csrrw x12, 951, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 951, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x83164a9e
	csrrw x12, 951, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 951, x6
	li x6, 0x83164a9e
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 951, x6
	li x6, 0xa7b7efbf
	bne x6, x12, csr_fail
	li x6, 0xe6429637
	csrrs x12, 951, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 951, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 951, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x97e1c152
	csrrc x12, 951, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 951, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 951, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 951, 0b11100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 951, 0b00101
	li x6, 0x0000001c
	bne x6, x12, csr_fail
	csrrsi x12, 951, 0b11010
	li x6, 0x0000001d
	bne x6, x12, csr_fail
	csrrsi x12, 951, 0b01100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 951, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 951, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 951, 0b10101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR8
	li x6, 0xa5a5a5a5
	csrrw x12, 952, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 952, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xb5e800ee
	csrrw x12, 952, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 952, x6
	li x6, 0xb5e800ee
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 952, x6
	li x6, 0xb5eda5ef
	bne x6, x12, csr_fail
	li x6, 0x71b06744
	csrrs x12, 952, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 952, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 952, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xb73d11ad
	csrrc x12, 952, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 952, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 952, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 952, 0b10100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 952, 0b00101
	li x6, 0x00000014
	bne x6, x12, csr_fail
	csrrsi x12, 952, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 952, 0b00011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 952, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 952, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 952, 0b10000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR9
	li x6, 0xa5a5a5a5
	csrrw x12, 953, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 953, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x7ce6cf6a
	csrrw x12, 953, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 953, x6
	li x6, 0x7ce6cf6a
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 953, x6
	li x6, 0xfde7efef
	bne x6, x12, csr_fail
	li x6, 0x5db76d50
	csrrs x12, 953, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 953, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 953, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xe039c23f
	csrrc x12, 953, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 953, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 953, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 953, 0b01000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 953, 0b00101
	li x6, 0x00000008
	bne x6, x12, csr_fail
	csrrsi x12, 953, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 953, 0b00000
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 953, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 953, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 953, 0b11110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR10
	li x6, 0xa5a5a5a5
	csrrw x12, 954, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 954, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xbe3c7341
	csrrw x12, 954, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 954, x6
	li x6, 0xbe3c7341
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 954, x6
	li x6, 0xbfbdf7e5
	bne x6, x12, csr_fail
	li x6, 0x4dcd8566
	csrrs x12, 954, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 954, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 954, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x81d6f159
	csrrc x12, 954, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 954, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 954, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 954, 0b10000
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 954, 0b00101
	li x6, 0x00000010
	bne x6, x12, csr_fail
	csrrsi x12, 954, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 954, 0b11100
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 954, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 954, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 954, 0b11011
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR11
	li x6, 0xa5a5a5a5
	csrrw x12, 955, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 955, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x86169bbe
	csrrw x12, 955, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 955, x6
	li x6, 0x86169bbe
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 955, x6
	li x6, 0xa7b7bfbf
	bne x6, x12, csr_fail
	li x6, 0xcbc3510f
	csrrs x12, 955, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 955, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 955, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xdcf6ec09
	csrrc x12, 955, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 955, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 955, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 955, 0b10001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 955, 0b00101
	li x6, 0x00000011
	bne x6, x12, csr_fail
	csrrsi x12, 955, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 955, 0b01000
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 955, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 955, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 955, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR12
	li x6, 0xa5a5a5a5
	csrrw x12, 956, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 956, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x9a55ab74
	csrrw x12, 956, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 956, x6
	li x6, 0x9a55ab74
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 956, x6
	li x6, 0xbff5aff5
	bne x6, x12, csr_fail
	li x6, 0x3ab6f7e7
	csrrs x12, 956, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 956, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 956, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xac7bc980
	csrrc x12, 956, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 956, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 956, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 956, 0b01101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 956, 0b00101
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 956, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 956, 0b11001
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 956, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 956, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 956, 0b10101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR13
	li x6, 0xa5a5a5a5
	csrrw x12, 957, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 957, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0x4c7bd3a4
	csrrw x12, 957, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 957, x6
	li x6, 0x4c7bd3a4
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 957, x6
	li x6, 0xedfff7a5
	bne x6, x12, csr_fail
	li x6, 0x897bd94e
	csrrs x12, 957, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 957, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 957, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x849898ed
	csrrc x12, 957, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 957, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 957, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 957, 0b01100
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 957, 0b00101
	li x6, 0x0000000c
	bne x6, x12, csr_fail
	csrrsi x12, 957, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 957, 0b00010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 957, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 957, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 957, 0b01110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR14
	li x6, 0xa5a5a5a5
	csrrw x12, 958, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 958, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xb3610a88
	csrrw x12, 958, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 958, x6
	li x6, 0xb3610a88
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 958, x6
	li x6, 0xb7e5afad
	bne x6, x12, csr_fail
	li x6, 0x1814363b
	csrrs x12, 958, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 958, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 958, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x94122f1d
	csrrc x12, 958, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 958, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 958, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 958, 0b01110
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 958, 0b00101
	li x6, 0x0000000e
	bne x6, x12, csr_fail
	csrrsi x12, 958, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 958, 0b11001
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 958, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 958, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 958, 0b00001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_PMPADDR15
	li x6, 0xa5a5a5a5
	csrrw x12, 959, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 959, x6
	li x6, 0xa5a5a5a5
	bne x6, x12, csr_fail
	li x6, 0xd7fad917
	csrrw x12, 959, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 959, x6
	li x6, 0xd7fad917
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 959, x6
	li x6, 0xf7fffdb7
	bne x6, x12, csr_fail
	li x6, 0x26e15b6e
	csrrs x12, 959, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 959, x6
	li x6, 0xffffffff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 959, x6
	li x6, 0x5a5a5a5a
	bne x6, x12, csr_fail
	li x6, 0x2e506fd9
	csrrc x12, 959, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 959, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 959, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 959, 0b01111
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 959, 0b00101
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 959, 0b11010
	li x6, 0x0000000f
	bne x6, x12, csr_fail
	csrrsi x12, 959, 0b01101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 959, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 959, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 959, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_FFLAGS
	li x6, 0xa5a5a5a5
	csrrw x12, 1, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 1, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x1002f175
	csrrw x12, 1, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 1, x6
	li x6, 0x00000015
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 1, x6
	li x6, 0x00000015
	bne x6, x12, csr_fail
	li x6, 0x5b47b8af
	csrrs x12, 1, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 1, x6
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 1, x6
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	li x6, 0xf51acefe
	csrrc x12, 1, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 1, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 1, 0b01001
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 1, 0b00101
	li x6, 0x00000009
	bne x6, x12, csr_fail
	csrrsi x12, 1, 0b11010
	li x6, 0x0000000d
	bne x6, x12, csr_fail
	csrrsi x12, 1, 0b01011
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 1, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 1, 0b11000
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_FRM
	li x6, 0xa5a5a5a5
	csrrw x12, 2, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x2d079f04
	csrrw x12, 2, x6
	li x6, 0x00000002
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2, x6
	li x6, 0x00000004
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x45235a4e
	csrrs x12, 2, x6
	li x6, 0x00000007
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2, x6
	li x6, 0x00000007
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2, x6
	li x6, 0x00000002
	bne x6, x12, csr_fail
	li x6, 0xa7093cbb
	csrrc x12, 2, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2, 0b01000
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrsi x12, 2, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 2, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrsi x12, 2, 0b00110
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrci x12, 2, 0b00101
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrci x12, 2, 0b11010
	li x6, 0x00000002
	bne x6, x12, csr_fail
	csrrci x12, 2, 0b11100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_FCSR
	li x6, 0xa5a5a5a5
	csrrw x12, 3, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3, x6
	li x6, 0x000000a5
	bne x6, x12, csr_fail
	li x6, 0x6a978105
	csrrw x12, 3, x6
	li x6, 0x0000005a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3, x6
	li x6, 0x00000005
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3, x6
	li x6, 0x000000a5
	bne x6, x12, csr_fail
	li x6, 0x2f940b9e
	csrrs x12, 3, x6
	li x6, 0x000000ff
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3, x6
	li x6, 0x000000ff
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3, x6
	li x6, 0x0000005a
	bne x6, x12, csr_fail
	li x6, 0xfb17c858
	csrrc x12, 3, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 3, 0b00011
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 3, 0b00101
	li x6, 0x00000003
	bne x6, x12, csr_fail
	csrrsi x12, 3, 0b11010
	li x6, 0x00000007
	bne x6, x12, csr_fail
	csrrsi x12, 3, 0b01010
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 3, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 3, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 3, 0b11001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_FTRAN
	li x6, 0xa5a5a5a5
	csrrw x12, 2048, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 2048, x6
	li x6, 0x00000025
	bne x6, x12, csr_fail
	li x6, 0x4b092c10
	csrrw x12, 2048, x6
	li x6, 0x0000005a
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 2048, x6
	li x6, 0x00000010
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 2048, x6
	li x6, 0x00000035
	bne x6, x12, csr_fail
	li x6, 0x8a9bb6cc
	csrrs x12, 2048, x6
	li x6, 0x0000007f
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 2048, x6
	li x6, 0x0000007f
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 2048, x6
	li x6, 0x0000005a
	bne x6, x12, csr_fail
	li x6, 0xfbaacf1e
	csrrc x12, 2048, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2048, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 2048, 0b11010
	li x6, 0x00000005
	bne x6, x12, csr_fail
	csrrwi x12, 2048, 0b10101
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrsi x12, 2048, 0b00101
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 2048, 0b11010
	li x6, 0x00000015
	bne x6, x12, csr_fail
	csrrsi x12, 2048, 0b01110
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2048, 0b00101
	li x6, 0x0000001f
	bne x6, x12, csr_fail
	csrrci x12, 2048, 0b11010
	li x6, 0x0000001a
	bne x6, x12, csr_fail
	csrrci x12, 2048, 0b10010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_CYCLE
	li x6, 0xa5a5a5a5
	csrrw x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x682be46b
	csrrw x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xdbc788f7
	csrrs x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x0de923f4
	csrrc x12, 3072, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3072, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3072, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3072, 0b00110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3072, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3072, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3072, 0b00011
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3072, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3072, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3072, 0b10111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_CYCLE_H
	li x6, 0xa5a5a5a5
	csrrw x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x6824d2ac
	csrrw x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x9c366129
	csrrs x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa670ab37
	csrrc x12, 3200, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3200, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3200, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3200, 0b01010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3200, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3200, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3200, 0b00110
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3200, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3200, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3200, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_INSTRET
	li x6, 0xa5a5a5a5
	csrrw x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa0b56aa9
	csrrw x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x02b9fe61
	csrrs x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa041b540
	csrrc x12, 3074, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3074, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3074, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3074, 0b10101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3074, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3074, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3074, 0b00100
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3074, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3074, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3074, 0b00001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	# CSR_INSTRET_H
	li x6, 0xa5a5a5a5
	csrrw x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrw x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x81155b50
	csrrw x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrs x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrs x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xe968b813
	csrrs x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0xa5a5a5a5
	csrrc x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x5a5a5a5a
	csrrc x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	li x6, 0x1f878f6c
	csrrc x12, 3202, x6
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3202, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3202, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrwi x12, 3202, 0b01111
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3202, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3202, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrsi x12, 3202, 0b10001
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3202, 0b00101
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3202, 0b11010
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrrci x12, 3202, 0b01011
	li x6, 0x00000000
	bne x6, x12, csr_fail
	csrr x12, 3202
	li x6, 0x00000000
	bne x6, x12, csr_fail

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
	
