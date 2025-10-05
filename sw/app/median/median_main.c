// See LICENSE for license details.

//**************************************************************************
// Median filter bencmark
//--------------------------------------------------------------------------
//
// This benchmark performs a 1D three element median filter. The
// input data (and reference data) should be generated using the
// median_gendata.pl perl script and dumped to a file named
// dataset1.h.

#include "util.h"

#include "median.h"


#define NUM_COUNTERS 2
static uintptr_t counters[NUM_COUNTERS];
static char* counter_names[NUM_COUNTERS];


void setStats(int enable)
{
  int i = 0;
#define READ_CTR(name) do { \
    while (i >= NUM_COUNTERS) ; \
    uintptr_t csr = read_csr(name); \
    if (!enable) { csr -= counters[i]; counter_names[i] = #name; } \
    counters[i++] = csr; \
  } while (0)

  READ_CTR(mcycle);
  READ_CTR(minstret);

#undef READ_CTR
}


//--------------------------------------------------------------------------
// Input/Reference Data

#include "dataset1.h"

//--------------------------------------------------------------------------
// Main



int main( int argc, char* argv[] )
{
  int results_data[DATA_SIZE];

#if PREALLOCATE
  // If needed we preallocate everything in the caches
  median( DATA_SIZE, input_data, results_data );
#endif

  // Do the filter
  setStats(1);
  median( DATA_SIZE, input_data, results_data );
  setStats(0);

  // Check the results
  return verify( DATA_SIZE, results_data, verify_data );
}
