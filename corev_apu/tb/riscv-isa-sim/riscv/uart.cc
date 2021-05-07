#include "devices.h"
#include "processor.h"

#define RBR  0
#define THR  0
#define IER  1
#define IIR  2
#define FCR  2
#define LCR  3
#define MCR  4
#define LSR  5
#define MSR  6
#define SCR  7
#define DLL  0
#define DLM  1

#define THRE 5 // transmit holding register empty
#define TEMT 6 // transmit holding register empty

uart_t::uart_t()
{
  dll = 0;
  dlm = 0;
  ier = 0;
  lcr = 0;
  mcr = 0;
  lsr = 0;
  msr = 0;
  scr = 0;
}

  // set {char}  0x10000004 = 0x00
  // set {char}  0x1000000C = 0x80
  // set {char}  0x10000000 = 0x1B
  // set {char}  0x10000004 = 0x00
  // set {char}  0x1000000C = 0x03
  // set {char}  0x10000008 = 0xC7
bool uart_t::load(reg_t addr, size_t len, uint8_t* bytes)
{
  // we do not support unaligned stores
  if ((addr & 0x3) != 0) {
    return false;
  }

  switch ((addr >> 0x2) & 0x7) {
    case THR:
              // access DLL
              if (lcr & 0x80) {
                bytes[0] = dll;
              } else {
                // TODO(zarubaf)
                // printf("%c", bytes[0]);
                bytes[0] = 0;
              }
              break;
    case IER:
              // access DLM
              if (lcr & 0x80) {
                bytes[0] = dlm;
              } else {
                bytes[0] = ier;
              }
              break;
    case IIR:
              if (fifo_enabled) {
                bytes[0] = 0xC0;
              } else {
                bytes[0] = 0x00;
              }
              break;
    case LCR:
              bytes[0] = lcr;
              break;
    case MCR:
              bytes[0] = mcr;
              break;
    case LSR:
              bytes[0] = lsr | (1 << THRE) | (1 << TEMT);
              break;
    case MSR:
              bytes[0] = msr;
              break;
    case SCR:
              bytes[0] = scr;
              break;
  }

  return true;
}

bool uart_t::store(reg_t addr, size_t len, const uint8_t* bytes)
{

  // we do not support unaligned stores
  if ((addr & 0x3) != 0) {
    return false;
  }

  switch ((addr >> 0x2) & 0x7) {
    case THR:
              // access DLL
              if (lcr & 0x80) {
                dll = bytes[0];
              } else {
                printf("%c", bytes[0]);
              }
              break;
    case IER:
              // access DLM
              if (lcr & 0x80) {
                dlm = bytes[0];
              } else {
                ier = bytes[0] & 0xF;
              }
              break;
    case FCR:
              if (bytes[0] & 0x1) {
                fifo_enabled = true;
              } else {
                fifo_enabled = false;
              }
              break;
    case LCR:
              lcr = bytes[0];
              break;
    case MCR:
              mcr = bytes[0] & 0x1F;
              break;
    case LSR:
              lsr = bytes[0];
              break;
    case MSR:
              msr = bytes[0];
              break;
    case SCR:
              scr = bytes[0];
              break;
  }

  return true;
}

