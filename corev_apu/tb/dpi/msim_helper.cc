// Author: Florian Zaruba
// Description: ModelSim Helper Functions

#include <vpi_user.h>

#include <vector>
#include <string>
#include <string.h>
#include <stdio.h>

// sanitize htif arguments
std::vector<std::string> sanitize_args() {
    bool permissive_on = false;

    s_vpi_vlog_info info;
    if (!vpi_get_vlog_info(&info))
      abort();

    std::vector<std::string> htif_args;

    // sanitize arguments
    for (int i = 1; i < info.argc; i++) {
      if (strcmp(info.argv[i], "+permissive") == 0) {
        permissive_on = true;
        // printf("Found permissive %s\n", info.argv[i]);
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
        // printf("Found permissive-off %s\n", info.argv[i]);
      }
    }

    return htif_args;
}
