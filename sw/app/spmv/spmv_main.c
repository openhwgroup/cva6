// See LICENSE for license details.

//**************************************************************************
// Double-precision sparse matrix-vector multiplication benchmark
//--------------------------------------------------------------------------

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

void spmv(int r, const double* val, const int* idx, const double* x,
          const int* ptr, double* y)
{
  for (int i = 0; i < r; i++)
  {
    int k;
    double yi0 = 0, yi1 = 0, yi2 = 0, yi3 = 0;
    for (k = ptr[i]; k < ptr[i+1]-3; k+=4)
    {
      yi0 += val[k+0]*x[idx[k+0]];
      yi1 += val[k+1]*x[idx[k+1]];
      yi2 += val[k+2]*x[idx[k+2]];
      yi3 += val[k+3]*x[idx[k+3]];
    }
    for ( ; k < ptr[i+1]; k++)
    {
      yi0 += val[k]*x[idx[k]];
    }
    y[i] = (yi0+yi1)+(yi2+yi3);
  }
}

//--------------------------------------------------------------------------
// Main

int main( int argc, char* argv[] )
{
  double y[R];

#if PREALLOCATE
  spmv(R, val, idx, x, ptr, y);
#endif

  setStats(1);
  spmv(R, val, idx, x, ptr, y);
  setStats(0);

  return verifyDouble(R, y, verify_data);
}
