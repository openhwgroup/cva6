// See LICENSE.SiFive for license details.

#include <fesvr/dtm.h>
#include <vpi_user.h>
#include <svdpi.h>
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
  bool permissive_on = false;

  if (!dtm) {
    s_vpi_vlog_info info;
    if (!vpi_get_vlog_info(&info))
      abort();

      std::vector<std::string> htif_args;

      // sanitize arguments
      for (int i = 1; i < info.argc; i++) {
        if (strcmp(info.argv[i], "+permissive") == 0) {
          permissive_on = true;
          printf("Found permissive %s\n", info.argv[i]);
        }

        // remove any two double pluses at the beginning (those are target arguments)
        if (info.argv[i][0] == '+' && info.argv[i][1] == '+' && strlen(info.argv[i]) > 3) {
            for (int j = 0; j < strlen(info.argv[i]) - 1; j++) {
              info.argv[i][j] = info.argv[i][j + 2];
            }
        }

        if (!permissive_on) {
          htif_args.push_back(info.argv[i]);
        }

        if (strcmp(info.argv[i], "+permissive-off") == 0) {
          permissive_on = false;
          printf("Found permissive-off %s\n", info.argv[i]);
        }
      }

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
