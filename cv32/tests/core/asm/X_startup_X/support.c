#include <stdio.h>
#include <string.h>

#include "support.h"

extern char _test_stdout;
extern int  _test_intc_machine_external;
extern int  _test_intc_machine_software;
extern int  _test_intc_machine_timer;
extern int  _intack;

// 
// Redefine standard write function
// arg0 FD, arg1 PTR, arg2 len
//
int _write (int fd, char *ptr, int len) {
    char *p = ptr;
    int i;
    
    for (i=0; i<len; i++) {
        _test_stdout = *p++;
    }
}

int _trap_Generic_Handler() {
    const char *message = "_trap_Generic_Handler Called\n";
    const char *ptr = message;
    _write(0, (char*)message, strlen(message));

    // return from exception
    asm("j _exit\n");
    return 0;
}

int _trap_Machine_Software_Interrupt () {
    const char *message = "_trap_Machine_Software_Interrupt Called\n";
    const char *ptr = message;
    _write(0, (char*)message, strlen(message));
    _intack = 3;

    return 0;
}

int _trap_Machine_Timer_Interrupt () {
    const char *message = "_trap_Machine_Timer_Interrupt Called\n";
    const char *ptr = message;
    _write(0, (char*)message, strlen(message));
    _intack = 7;

    return 0;
}

int _trap_Machine_External_Interrupt () {
    const char *message = "_trap_Machine_External_Interrupt Called\n";
    const char *ptr = message;
    _write(0, (char*)message, strlen(message));
    _intack = 11;

    return 0;
}

void enable_Machine_External_Interrupt() {
    asm(
        "    li        t0, (0x1 << 11) \n"
        "    csrs      mie, t0 \n"
        "    li        t0, (0x1 << 3) \n"
        "    csrs      mstatus, t0 \n"
    );
    return;
}

void disable_Machine_External_Interrupt() {
    asm(
        "    li        t0, (0x1 << 11) \n"
        "    csrc      mie, t0 \n"
    );
    return;
}

void enable_Machine_Software_Interrupt() {
    asm(
        "    li        t0, (0x1 << 3) \n"
        "    csrs      mie, t0 \n"
        "    li        t0, (0x1 << 3) \n"
        "    csrs      mstatus, t0 \n"
    );
    return;
}

void disable_Machine_Software_Interrupt() {
    asm(
        "    li        t0, (0x1 << 3) \n"
        "    csrc      mie, t0 \n"
    );
    return;
}

void enable_Machine_Timer_Interrupt() {
    asm(
        "    li        t0, (0x1 << 7) \n"
        "    csrs      mie, t0 \n"
        "    li        t0, (0x1 << 3) \n"
        "    csrs      mstatus, t0 \n"
    );
    return;
}

void disable_Machine_Timer_Interrupt() {
    asm(
        "    li        t0, (0x1 << 7) \n"
        "    csrc      mie, t0 \n"
    );
    return;
}

void enableVEC() {
    asm(
        "    csrr      t0, mstatus       \n"
        "    li        t1, (0x1 << 23)   \n"
        "    or        t1, t1, t0        \n"
        "    csrw      mstatus, t1       \n"
    );
    return;
}

void setupVEC() {
    asm(".word 0x00b7f2d7 \n");
    return;
}
void illegalOP() {
    asm(".word 0x00000000 \n");
    return;
}

void setINTC_machine_external(int cycles) {
    _test_intc_machine_external = cycles;
}
void setINTC_machine_software(int cycles) {
    _test_intc_machine_software = cycles;
}
void setINTC_machine_timer(int cycles) {
    _test_intc_machine_timer = cycles;
}
void _clrINTC_machine_external() {
    _test_intc_machine_external = 0;
}
void _clrINTC_machine_software() {
    _test_intc_machine_software = 0;
}
void _clrINTC_machine_timer() {
    _test_intc_machine_timer = 0;
}
