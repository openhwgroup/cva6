// See LICENSE for license details.

//**************************************************************************
// Vector-vector add benchmark
//--------------------------------------------------------------------------
//
// This benchmark uses adds to vectors and writes the results to a
// third vector. The input data (and reference data) should be
// generated using the vvadd_gendata.pl perl script and dumped
// to a file named dataset1.h.
 
#include "util.h"


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
// vvadd function

void vvadd( int n, int a[], int b[], int c[] )
{
  int i;
  for ( i = 0; i < n; i++ )
    c[i] = a[i] + b[i];
}

//--------------------------------------------------------------------------
// Main

int main( int argc, char* argv[] )
{
  int results_data[DATA_SIZE];

#if PREALLOCATE
  // If needed we preallocate everything in the caches
  vvadd( DATA_SIZE, input1_data, input2_data, results_data );
#endif

  // Do the vvadd
  setStats(1);
  vvadd( DATA_SIZE, input1_data, input2_data, results_data );
  setStats(0);

  // Check the results
  return verify( DATA_SIZE, results_data, verify_data );
}
