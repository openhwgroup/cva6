#include "stdlib.h"
#include "dataset.h"

void __attribute__((noinline)) vvadd(int coreid, int ncores, size_t n, const data_t* x, const data_t* y, data_t* z)
{
  size_t i;
  size_t leftover = n % (n / ncores);
  for (i = coreid * (n / ncores); i < (coreid + 1) * (n / ncores); i++) {
    z[i] = x[i] + y[i];
  }
  for (i = (n - leftover) + coreid; i < n; i += ncores) {
    z[i] = x[i] + y[i];
  }
}
