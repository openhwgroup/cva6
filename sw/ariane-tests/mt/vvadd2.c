#include "stdlib.h"
#include "dataset.h"

void __attribute__((noinline)) vvadd(int coreid, int ncores, size_t n, const data_t* x, const data_t* y, data_t* z)
{
   size_t i;
   for (i = coreid; i < n; i += 2*ncores) {
      z[i] = x[i] + y[i];
      z[i+ncores] = x[i+ncores] + y[i+ncores];
   }
}
