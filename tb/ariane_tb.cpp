// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at

//   http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

#include "svdpi.h"
#include "Variane_wrapped__Dpi.h"

#include <stdio.h>
#include "simmem.h"
#include <fesvr/htif.h>
#include <fesvr/memif.h>
#include <fesvr/htif_hexwriter.h>
#include <time.h>
#include <iostream>
#include <string>
#include <fesvr/option_parser.h>

std::unique_ptr<simmem_t> htif;
bool stop_sim = false;

extern unsigned long long read_uint64 (unsigned long long address) {

  // as we do not have physical memory protection at the moment check here for invalid accesses
  // in the soc this is done by the AXI bus
  if (address < 0x80000000) {
    return 0xdeadbeafdeadbeef;
  }

  return htif->memif().read_uint64(address);
}

extern void write_uint64 (unsigned long long address, unsigned long long data) {
  htif->memif().write_uint64(address, data);
}

extern unsigned long long get_tohost_address() {
  return htif->get_tohost_address();
}

extern unsigned long long get_fromhost_address() {
  return htif->get_fromhost_address();
}

static void help()
{
  fprintf(stderr, "usage: ariane C verilator simulator [host options] <target program> [target options]\n");
  fprintf(stderr, "Host Options:\n");
  fprintf(stderr, "  --vcd=<file>              Dump VCD trace to file\n");
  fprintf(stderr, "  --label=<label>           Pass a label to the program\n");
  fprintf(stderr, "  -p                        Show simulation performance counters\n");
  fprintf(stderr, "  -v                        Verbose\n");
  exit(1);
}

// This is a 64-bit integer to reduce wrap over issues and
// allow modulus.  You can also use a double, if you wish.

double sc_time_stamp () {       // Called by $time in Verilog
    return htif->main_time;     // converts to double, to match
                                // what SystemC does
}

int main(int argc, char **argv) {

  const char *vcd_file = NULL, *label = NULL;
  bool dump_perf = false, verbose= false;

  option_parser_t parser;
  parser.help(&help);
  parser.option('h', 0, 0, [&](const char* s){help();});
  parser.option('p', 0, 0, [&](const char* s){dump_perf = true;});
  parser.option('v', 0, 0, [&](const char* s){verbose = true;});
  parser.option(0, "vcd", 1, [&](const char* s){vcd_file = s;});
  parser.option(0, "label", 1, [&](const char* s){label = s;});

  auto argv1 = parser.parse(argv);
  std::vector<std::string> htif_args(argv1, (const char*const*)argv + argc);

  htif.reset(new simmem_t(htif_args, 0x80000000, 8, 2097152));

  htif->set_vcd(vcd_file);
  htif->set_label(label);
  htif->start();

  clock_t t;
  t = clock();

  htif->run();

  t = clock() - t;

  if (dump_perf) {
    fprintf(stderr, "Elapsed Time: %f seconds\n", t*1.0/CLOCKS_PER_SEC);
    fprintf(stderr, "Cycles: %2.f \n", htif->main_time/10.0);
    fprintf(stderr, "Cycles/s: %2.f\n", (htif->main_time*1.0)/(t*10.0/CLOCKS_PER_SEC));
  }
  exit(0);
}
