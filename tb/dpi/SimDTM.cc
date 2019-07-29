// See LICENSE.SiFive for license details.
#include "msim_helper.h"

#include <fesvr/dtm.h>
#include <vpi_user.h>
#include <svdpi.h>
#include <stdio.h>
#include <string.h>
#include <vector>

extern "C" int debug_tick
(
  unsigned char* debug_req_valid,
  unsigned char  debug_req_ready,
  int*           debug_req_bits_addr,
  int*           debug_req_bits_op,
  int*           debug_req_bits_data,
  unsigned char  debug_resp_valid,
  unsigned char* debug_resp_ready,
  int            debug_resp_bits_resp,
  int            debug_resp_bits_data
)
{
  return 0;
}
