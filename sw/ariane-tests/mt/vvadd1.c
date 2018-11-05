#include "stdlib.h"
#include "dataset.h"

void __attribute__((noinline)) vvadd(int coreid, int ncores, size_t n, const data_t* x, const data_t* y, data_t* z)
{
   size_t i;
   for (i = coreid*4; i < n; i += 8*ncores) {
      z[i]   = x[i]   + y[i];
      z[i+1] = x[i+1] + y[i+1];
      z[i+2] = x[i+2] + y[i+2];
      z[i+3] = x[i+3] + y[i+3];
      z[i+ncores*4]   = x[i+ncores*4]   + y[i+ncores*4];
      z[i+ncores*4+1] = x[i+ncores*4+1] + y[i+ncores*4+1];
      z[i+ncores*4+2] = x[i+ncores*4+2] + y[i+ncores*4+2];
      z[i+ncores*4+3] = x[i+ncores*4+3] + y[i+ncores*4+3];
   }
}
