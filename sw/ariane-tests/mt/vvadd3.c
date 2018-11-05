#include "stdlib.h"
#include "dataset.h"

void __attribute__((noinline)) vvadd(int coreid, int ncores, size_t n, const data_t* x, const data_t* y, data_t* z)
{
  data_t* to = &z[coreid * (n / ncores)];
  const data_t* from1 = &x[coreid * (n / ncores)];
  const data_t* from2 = &y[coreid * (n / ncores)];
  size_t count = n / ncores;
  size_t c = (count + 7) / 8;
  switch(count % 8) {
    case 0: do {  *to++ = *from1++ + *from2++;
    case 7:       *to++ = *from1++ + *from2++;
    case 6:       *to++ = *from1++ + *from2++;
    case 5:       *to++ = *from1++ + *from2++;
    case 4:       *to++ = *from1++ + *from2++;
    case 3:       *to++ = *from1++ + *from2++;
    case 2:       *to++ = *from1++ + *from2++;
    case 1:       *to++ = *from1++ + *from2++;
  } while(--c > 0);
  }
}
