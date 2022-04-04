# Google UVM Generated Test
# Extracted from riscv_compliance_tests/riscv_test.h
.set print_port,   0x00800000
.set test_ret_val, 0x008000c0
.section .data
.global test_results
test_results:
	.word 123456789

#TODO: figure out how to move this to the end of the program
#.section .text
#quick_fast_exit:
#                  /* print "DONE\n" */
#                  lui a0,print_port>>12
#                  addi a1,zero,'D'
#                  addi a2,zero,'O'
#                  addi a3,zero,'N'
#                  addi a4,zero,'E'
#                  addi a5,zero,'\n'
#                  sw a1,0(a0)
#                  sw a2,0(a0)
#                  sw a3,0(a0)
#                  sw a4,0(a0)
#                  sw a5,0(a0)
#
#                  li a0, CV_VP_STATUS_FLAGS_OFFSET
#                  lw a1, test_results /* report result */
#                  sw a1,0(a0)
#
#                  wfi  /* we are done */
