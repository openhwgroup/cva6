#ifndef _SUPPORT_H_
#define _SUPPORT_H_

int  _trap_Generic_Handler();

int  _trap_Machine_Software_Interrupt();
int  _trap_Machine_Timer_Interrupt();
int  _trap_Machine_External_Interrupt();


void enable_Machine_External_Interrupt();
void enable_Machine_Timer_Interrupt();
void enable_Machine_Software_Interrupt();

void disable_Machine_External_Interrupt();
void disable_Machine_Timer_Interrupt();
void disable_Machine_Software_Interrupt();

void enableVEC();
void setupVEC();

void illegalOP();

void setINTC_machine_external(int cycles);
void setINTC_machine_timer(int cycles);
void setINTC_machine_software(int cycles);
void _clrINTC_machine_external();
void _clrINTC_machine_timer();
void _clrINTC_machine_software();

#endif
