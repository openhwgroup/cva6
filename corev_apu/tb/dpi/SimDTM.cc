// See LICENSE.SiFive for license details.
#include "msim_helper.h"

#include <fesvr/dtm.h>
#include <vpi_user.h>
#include <svdpi.h>
#include <iostream>
#include <stdio.h>
#include <string.h>
#include <vector>

dtm_t* dtm;

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

  if (!dtm) {

      std::vector<std::string> htif_args = sanitize_args();

      // convert vector to argc and argv
      int argc = htif_args.size() + 1;
      char * argv[argc];
      argv[0] = (char *) "htif";
      for (unsigned int i = 0; i < htif_args.size(); i++) {
        argv[i+1] = (char *) htif_args[i].c_str();
      }

      dtm = new dtm_t(argc, argv);
  }

  dtm_t::resp resp_bits;
  resp_bits.resp = debug_resp_bits_resp;
  resp_bits.data = debug_resp_bits_data;

  dtm->tick
  (
    debug_req_ready,
    debug_resp_valid,
    resp_bits
  );

  *debug_resp_ready = dtm->resp_ready();
  *debug_req_valid = dtm->req_valid();
  *debug_req_bits_addr = dtm->req_bits().addr;
  *debug_req_bits_op = dtm->req_bits().op;
  *debug_req_bits_data = dtm->req_bits().data;

  return dtm->done() ? (dtm->exit_code() << 1 | 1) : 0;
}

extern "C" void dtm_set_exitcode(unsigned int code)
{
  if (!dtm) {
    std::cerr << "*** Cannot return the exit code without a running DTM!\n";
    return;
  }

  dtm->set_exitcode(code);
}

extern "C" unsigned long int dtm_get_tohost_addr(const char *binary /* unused when using HTIF */)
{
  if (!dtm) {
    std::cerr << "*** Cannot determine DTM 'tohost' address without a running DTM!\n";
    return 0;
  }

  unsigned long int tohost_addr = dtm->get_tohost_addr();
  std::cerr << "### Calling dtm->get_tohost_addr() for file '" << binary << "', value returned is 0x" << std::hex << tohost_addr << std::dec << "\n";
  return dtm->get_tohost_addr();
}