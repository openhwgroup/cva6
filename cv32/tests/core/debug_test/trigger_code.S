.section .trigger_code_sect, "ax"
.set test_ret_val, 0x20000000
.set test_fail, 0x1

.global _trigger_exit
.global _trigger_test
.global _trigger_code
.type _trigger_code, @function
     // We will trigger on the _trigger_code addess
	// We should not expect the first instruction to execute
	// The debugger code will move the PC to the trigger_exit_code
	// Which essentially avoid executing all of the code in the trigger_code
_trigger_code:        
        add a2,a0,a1
        ret
_trigger_exit:        
        ret
_trigger_test:        
        addi sp,sp,-30
        sw t0, 0(sp)
        sw t1, 4(sp)
        sw a0, 8(sp)
        sw a1, 12(sp)
        sw a2, 16(sp)
        sw ra, 20(sp)

	// a0 holds input to function (expect trigger)
	mv t1, a0

	// Load up some random data to add
	li a0, 7893
	li a1, 1452
	li a2,  191 // a2 value will be overwrriten by _trigger_code
	mv t2,  a2  // keep a copy of the value to compare against
	
	// Call function that will have a trigger match
	//   If no trigger match, then a2=a0+a1
	//   Else if trigger matched, then a2 is not modified
	jal ra, _trigger_code

	// if (expect trigger) check against original value (in t2)
	bne t1 ,x0, __trigger_check
	// else
	// trigger match not expected, function executes as normal
	// set execpted value to t2 = a0 + a1
	add t2, a0, a1
__trigger_check:	
	beq t2,a2,__trigger_done
__trigger_fail:	
        li a0, test_ret_val
        li t0, 1
        sw t0, 0(a0)
__trigger_done:	
        lw t0, 0(sp)
        lw t1, 4(sp)
        lw a0, 8(sp)
        lw a1, 12(sp)
        lw a2, 16(sp)
        lw ra, 20(sp)
        addi sp,sp,30
	ret
