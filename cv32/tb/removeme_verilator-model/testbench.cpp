// Copyright 2017 Embecosm Limited <www.embecosm.com>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Simple Verilator model test bench
// Contributor Jeremy Bennett <jeremy.bennett@embecosm.com>
// Contributor Graham Markall <graham.markall@embecosm.com>


#include "verilated.h"
#include "verilated_vcd_c.h"
#include "Vtop.h"
#include "Vtop__Syms.h"

#include <iostream>
#include <cstdint>
#include <cstdlib>

#include<stdio.h>

#define STARTprogrammADDR   0x80
#define BASEdebugPROGaddr   0x0A0800
#define STARTdebugPROGaddr  0x0A0800
#define FlagADDRESSbase     0x0A0400
#define wheretoADDRESS      0x0A0300

#define FLAGresume          0x02
#define FLAGgo              0x01
#define FLAGloop            0x00


using std::cout;
using std::cerr;
using std::endl;

// Count of clock ticks

static vluint64_t  cpuTime = 0;



static uint64_t mCycleCnt = 0;

Vtop *cpu;
VerilatedVcdC * tfp;

unsigned int OLDREGFILE[32]={0},
             REGFILE[32]={0};

void REGfilePrint()
{
      unsigned int changeregfile=0;
      for (int alfa=0;alfa<32;alfa++)
      {
          REGFILE[alfa]=cpu->top->readREGfile(alfa);
          if (REGFILE[alfa]!=OLDREGFILE[alfa])
          {
             changeregfile|=(1<<alfa);
          }
      }
      
      printf("\n           %s",std::string(9*8+2,'-').c_str());
      printf("\n           |%4d %8d %8d %8d %8d %8d %8d %8d     |",0,1,2,3,4,5,6,7);
      printf("\n       %s",std::string(9*8+2+4,'-').c_str());
      //printf("\e[102m"); //green
      printf("\n       | 0 |%.8s ","--zero--");
      for (int alfa=1;alfa<8;alfa++)
      {
          if(changeregfile & (1<<alfa))
          {
             printf("\e[30;42m%.8x\e[39;0m ",cpu->top->readREGfile(alfa));
          }
          else
          {
             printf("%.8x ",cpu->top->readREGfile(alfa));
          }

      }
      printf("| R f\n       | 8 |");
      for (int alfa=8;alfa<16;alfa++)
      {
          if(changeregfile & (1<<alfa))
          {
             printf("\e[30;42m%.8x\e[39;0m ",cpu->top->readREGfile(alfa));
          }
          else
          {
             printf("%.8x ",cpu->top->readREGfile(alfa));
          }
      }
      printf("| E i\n       |16 |");
      for (int alfa=16;alfa<24;alfa++)
      {
          if(changeregfile & (1<<alfa))
          {
             printf("\e[30;42m%.8x\e[39;0m ",cpu->top->readREGfile(alfa));
          }
          else
          {
             printf("%.8x ",cpu->top->readREGfile(alfa));
          }
      }
      printf("| G l\n       |24 |");
      for (int alfa=24;alfa<32;alfa++)
      {
          if(changeregfile & (1<<alfa))
          {
             printf("\e[30;42m%.8x\e[39;0m ",cpu->top->readREGfile(alfa));
          }
          else
          {
             printf("%.8x ",cpu->top->readREGfile(alfa));
          }
      }
      for (int alfa=1;alfa<32;alfa++)
      {
         OLDREGFILE[alfa]=REGFILE[alfa];
      }
      
      printf("|   e");
      printf("\n       %s",std::string(9*8+2+4,'-').c_str());
      //printf("\e[49m"); //default
}
// Clock the CPU for a given number of cycles, dumping to the trace file at
// each clock edge.
void clockSpin(uint32_t cycles)
{
  for (uint32_t i = 0; i < cycles; i++)
  {
      cpu->clk_i = 0;
      cpu->eval ();
      cpuTime += 5;
      tfp->dump (cpuTime);
      cpu->clk_i = 1;
      cpu->eval ();
      cpuTime += 5;
      tfp->dump (cpuTime);
      mCycleCnt++;

      //printf("     test: %7.2f ns. pc_i f d e: 0x%5x  0x%5x  0x%5x  \n", sc_time_stamp(), cpu->top->readADDtestPC_IF(),cpu->top->readADDtestPC_ID(),cpu->top->readADDtestPC_EX());
      printf("   test: %7.2f ns. pc_i f d e: ",sc_time_stamp()); 
 
      if( (cpu->top->readADDtestPC_IF()&0xFF0000) == 0x0A0000 )
      	printf("\e[7m0x%.8x\e[27m   ", cpu->top->readADDtestPC_IF());
      else
        printf("0x%.8x   ", cpu->top->readADDtestPC_IF());

      if( (cpu->top->readADDtestPC_ID()&0xFF0000) == 0x0A0000 )
      	printf("\e[7m0x%.8x\e[27m   ", cpu->top->readADDtestPC_ID());
      else
        printf("0x%.8x   ", cpu->top->readADDtestPC_ID());

      if( (cpu->top->readADDtestPC_EX()&0xFF0000) == 0x0A0000 )
      	printf("\e[7m0x%.8x\e[27m   "   , cpu->top->readADDtestPC_EX());
      else
        printf("0x%.8x   ", cpu->top->readADDtestPC_EX());

      
      REGfilePrint();
      

      cout << endl;
  }
}



// Write some program code into memory:
//
// ; Store a word to memory first:
// li a5, 64
// li a4, 102
// sw a4, 0(a5)
// ; Repeated <repeat_factor> times (20 at present)
//
// ; Then do something a bit like _exit(0)
// li a1, 0
// li a2, 0
// li a3, 0
// li a7, 93
// ecall
//
// Execution begins at 0x80, so that's where we write our code.
void loadProgram(uint32_t addr)
{
  //uint32_t addr = 0x80;
  cout << "\e[93m   Start program address : 0x" << std::hex << addr << "\e[39m" <<endl;
  uint32_t repeat_factor = 20;
  for (size_t i = 0; i < repeat_factor; i++)
  {
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x0, 0x93);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1, 0x07);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2, 0x00);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3, 0x04);

    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4, 0x13);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5, 0x07);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6, 0x60);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x7, 0x06);

    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x8, 0x23);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x9, 0xa0);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xa, 0xe7);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xb, 0x00);

    addr += 0xC;
  }

//write all register with 0xffff_ffff
printf("addr (init new code): %d\n",addr); 
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 0, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 1, 0x00 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 2, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 3, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 4, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 5, 0x01 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 6, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 7, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 8, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 9, 0x01 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 10, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 11, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 12, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 13, 0x02 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 14, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 15, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 16, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 17, 0x02 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 18, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 19, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 20, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 21, 0x03 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 22, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 23, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 24, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 25, 0x03 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 26, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 27, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 28, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 29, 0x04 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 30, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 31, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 32, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 33, 0x04 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 34, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 35, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 36, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 37, 0x05 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 38, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 39, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 40, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 41, 0x05 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 42, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 43, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 44, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 45, 0x06 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 46, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 47, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 48, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 49, 0x06 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 50, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 51, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 52, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 53, 0x07 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 54, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 55, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 56, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 57, 0x07 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 58, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 59, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 60, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 61, 0x08 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 62, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 63, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 64, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 65, 0x08 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 66, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 67, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 68, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 69, 0x09 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 70, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 71, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 72, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 73, 0x09 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 74, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 75, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 76, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 77, 0x0a );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 78, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 79, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 80, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 81, 0x0a );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 82, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 83, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 84, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 85, 0x0b );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 86, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 87, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 88, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 89, 0x0b );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 90, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 91, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 92, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 93, 0x0c );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 94, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 95, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 96, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 97, 0x0c );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 98, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 99, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 100, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 101, 0x0d );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 102, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 103, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 104, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 105, 0x0d );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 106, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 107, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 108, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 109, 0x0e );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 110, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 111, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 112, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 113, 0x0e );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 114, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 115, 0xff );
			
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 116, 0x13 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 117, 0x0f );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 118, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 119, 0xff );

	cpu->top->ram_i->dp_ram_i->writeByte (addr + 120, 0x93 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 121, 0x0f );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 122, 0xf0 );
	cpu->top->ram_i->dp_ram_i->writeByte (addr + 123, 0xff );
printf("addr (end new code): %d\n",addr+123);
//end write all register with 0xffff_fff
   addr=addr+124;
printf("addr (after addr+120): %d\n",addr);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x0, 0x93);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1, 0x05);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3, 0x00);

  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4, 0x13);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5, 0x06);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x7, 0x00);

  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x8, 0x93);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x9, 0x06);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xa, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xb, 0x00);

  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xc, 0x93);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xd, 0x08);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xe, 0xd0);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xf, 0x05);

/*
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x10, 0x73);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x11, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x12, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x13, 0x00);
*/
printf("addr (after 4 instructions) : %d\n",addr);
  addr=addr+16;
printf("addr (after addr+20): %d\n",addr);
  for (size_t i = 0; i < repeat_factor; i++)
  {
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x0, 0x93);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1, 0x07);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2, 0x00);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3, 0x04);

    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4, 0x13);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5, 0x07);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6, 0x60);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x7, 0x06);

    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x8, 0x23);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x9, 0xa0);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xa, 0xe7);
    cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xb, 0x00);

    addr += 0xC;
  }
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x0, 0x93);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1, 0x05);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3, 0x00);

  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4, 0x13);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5, 0x06);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x7, 0x00);

  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x8, 0x93);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x9, 0x06);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xa, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xb, 0x00);

  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xc, 0x93);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xd, 0x08);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xe, 0xd0);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xf, 0x05);


  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x10, 0x73);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x11, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x12, 0x00);
  cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x13, 0x00);

  addr+=20;
printf("addr end: %d\n",addr);
 
// print Instruc MEM
   for(unsigned int alfa=0x80; alfa < addr; alfa+=4)
   {
     printf("INSTR MEM: %.4d (0x%.4x)   0x%2.2x%2.2x_%2.2x%2.2x\n",alfa,
                                                                   alfa,
                                                                   cpu->top->ram_i->dp_ram_i->readByte(alfa+3),
                                                                   cpu->top->ram_i->dp_ram_i->readByte(alfa+2),
                                                                   cpu->top->ram_i->dp_ram_i->readByte(alfa+1),
                                                                   cpu->top->ram_i->dp_ram_i->readByte(alfa+0) 
     );
   }
}


void DebugFLAG(uint32_t hartID,uint8_t debugFLAG)
{
  cout << "\e[31m hart " << hartID << "!  FLAG hart address: " << std::hex <<FlagADDRESSbase + hartID << " (debugBASEaddr + 0x400 + hartid)" <<"\e[39m" << endl;
  cpu->top->ram_i->dp_ram_i->writeByte (FlagADDRESSbase + hartID, debugFLAG ); //2=resume:1=go;0=loop 
}

void whereto()
{

   //jalr zero,a0,0x804  --> resume
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x0, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x1, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x2, 0x40 );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x3, 0x50 );

/*
   //jalr zero,a0,0x368  --> prog buff base
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x0, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x1, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x2, 0x80 );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x3, 0x06 );

   //jalr zero,a0,0x350  --> Abstract cmd base
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x0, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x1, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x2, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (wheretoADDRESS + 0x3, 0x05 );
*/
}

void loadDebugProgram(uint32_t addr)
{
  //20 bits: max 0x0F_FFFF
  //      debug: 0x0A_0800
  //uint32_t addr = 0x0A0800; //real addr is 0x1a11_0800
 
  cout << "\e[93m   Start debug program address : 0x" << std::hex << addr << "\e[39m" <<endl;  

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x0, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2, 0xc0 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x7, 0x06 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x8, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x9, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xa, 0x40 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xb, 0x04 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xc, 0x13 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xd, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xe, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0xf, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x10, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x11, 0x10 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x12, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x13, 0x7b );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x14, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x15, 0x10 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x16, 0x35 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x17, 0x7b );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x18, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x19, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1a, 0x40 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1b, 0xf1 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1c, 0x37 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1d, 0x05 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1e, 0x0a );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x1f, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x20, 0x23 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x21, 0x20 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x22, 0x85 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x23, 0x10 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x24, 0x33 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x25, 0x04 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x26, 0xa4 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x27, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x28, 0x03 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x29, 0x44 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2a, 0x04 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2b, 0x40 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2c, 0x13 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2d, 0x74 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2e, 0x14 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x2f, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x30, 0x63 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x31, 0x12 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x32, 0x04 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x33, 0x02 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x34, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x35, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x36, 0x40 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x37, 0xf1 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x38, 0x33 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x39, 0x04 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3a, 0xa4 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3b, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3c, 0x03 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3d, 0x44 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3e, 0x04 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x3f, 0x40 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x40, 0x13 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x41, 0x74 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x42, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x43, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x44, 0xe3 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x45, 0x10 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x46, 0x04 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x47, 0xfc );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x48, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x49, 0xf0 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4a, 0x1f );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4b, 0xfd );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4c, 0x23 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4d, 0x26 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4e, 0x05 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x4f, 0x10 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x50, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x51, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x52, 0x10 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x53, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x54, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x55, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x56, 0x20 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x57, 0x7b );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x58, 0x23 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x59, 0x22 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5a, 0x05 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5b, 0x10 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5c, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5d, 0x25 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5e, 0x30 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x5f, 0x7b );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x60, 0x6f );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x61, 0xf0 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x62, 0x1f );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x63, 0xaa );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x64, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x65, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x66, 0x40 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x67, 0xf1 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x68, 0x37 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x69, 0x05 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6a, 0x0a );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6b, 0x00 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6c, 0x23 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6d, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6e, 0x85 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x6f, 0x10 );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x70, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x71, 0x24 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x72, 0x20 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x73, 0x7b );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x74, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x75, 0x25 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x76, 0x30 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x77, 0x7b );

   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x78, 0x73 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x79, 0x00 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x7a, 0x20 );
   cpu->top->ram_i->dp_ram_i->writeByte (addr + 0x7b, 0x7b );


 
}


int
main (int    argc,
      char * argv[])
{
  // Instantiate the model
  cpu = new Vtop;

  // Open VCD
  Verilated::traceEverOn (true);
  tfp = new VerilatedVcdC;
  cpu->trace (tfp, 99);
  tfp->open ("model.vcd");

  cout << "\e[32m"; //green
  cout << " irq_i            = 0\n";
  cout << " debug_req_i      = 0\n";
  cout << " fetch_enable_i   = 0\n";
  cout << "\e[39m"; //default

  // Fix some signals for now.
  cpu->irq_i          = 0;
  cpu->debug_req_i    = 0;
  cpu->fetch_enable_i = 0;


  cout << "\e[33mLoad Programm to ram:\e[39m\n";
  // Put a few instructions in memory
  loadProgram(STARTprogrammADDR);

  // Put debug instruction in memory
  loadDebugProgram(STARTdebugPROGaddr);

  // Cycle through reset
  cpu->rstn_i = 0;
  clockSpin(5);
  cpu->rstn_i = 1;

  // Let things run for a few cycles while the CPU 
  clockSpin(5);


  cout << "\e[34mTest resume\e[39m" << endl;

  //fetch enable:
  cout << "\e[32m"; //green
  cout << " fetch_enable_i   = 1\n";
  cout << "\e[39m"; //default
  cpu->fetch_enable_i = 1;

  cout << "Cycling clock to run for a few instructions" << endl;
  clockSpin(96);

  cout << "  Debug req:" <<endl;

  cpu->debug_req_i = 1;
  cout << " \e[32mdebug_req = 1\e[39m" << endl;
  clockSpin(2);
  cpu->debug_req_i = 0;
  cout << " \e[32mdebug_req = 0\e[39m" << endl;

  //resume=2: 
  DebugFLAG(0x03e0,FLAGgo);

  //whereto
  whereto();

  clockSpin(82);
 

  // Close VCD

  tfp->close ();

  // Tidy up

  delete tfp;
  delete cpu;

}

//! Function to handle $time calls in the Verilog

double
sc_time_stamp ()
{
  return cpuTime;

}

// Local Variables:
// mode: C++
// c-file-style: "gnu"
// show-trailing-whitespace: t
// End:
