#include "devices.h"
#include "processor.h"
#include <fstream>

dump_t::dump_t() : ofs("dump.bin")
{
  // printf("Calling Dump\n");
}

bool dump_t::load(reg_t addr, size_t len, uint8_t* bytes)
{
  return true;
}

bool dump_t::store(reg_t addr, size_t len, const uint8_t* bytes)
{
  // printf("DUmpping\n");
  ofs.write(reinterpret_cast<const char *>(bytes), len);
  return true;
}

