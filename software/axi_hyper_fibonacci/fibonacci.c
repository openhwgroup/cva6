/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* 
 * Mantainer: Luca Valente, luca.valente2@unibo.it
 */

//#include "util.h"
#include <stdio.h>
#include <stdlib.h>
#define N 20

const int RESULT_FIB[N] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181};

int main(int argc, char const *argv[]) {
  int * b;
  b=0xC1003080;
  int i;
  b[0]=0;
  b[1]=1;
  b[2]=1;
  for(i=3;i<10;i++)
    {
      b[i]=b[i-1]+b[i-2];
      if(b[i]!=RESULT_FIB[i])
        return 1;
    }

  return 0;
}
