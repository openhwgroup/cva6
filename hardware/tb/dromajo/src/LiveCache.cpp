// Licensed under the Apache License, Version 2.0 (the "License")
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// THIS FILE IS BASED ON ESESC SOURCE CODE WHICH IS DISTRIBUTED UNDER
// THE FOLLOWING LICENSE:
//
// copyright and includes {{{1
// Contributed by Sina Hassani
//                Jose Renau
//
// The ESESC/BSD License
//
// Copyright (c) 2005-2015, Regents of the University of California and
// the ESESC Project.
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
//   - Redistributions of source code must retain the above copyright notice,
//   this list of conditions and the following disclaimer.
//
//   - Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the distribution.
//
//   - Neither the name of the University of California, Santa Cruz nor the
//   names of its contributors may be used to endorse or promote products
//   derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.


#include "LiveCacheCore.h"

//#define MTRACE(a...)   do{ fprintf(stderr,"@%lld %s %d 0x%x:",(long long int)globalClock,getName(), (int)mreq->getID(), (unsigned
// int)mreq->getAddr()); fprintf(stderr,##a); fprintf(stderr,"\n"); }while(0)
#define MTRACE(a...)

LiveCache::LiveCache(const std::string &_name, int size)
 :name(_name) {

  cacheBank    = CacheType::create(size, 16, 64, "LRU", false);
  lineSize     = cacheBank->getLineSize();
  lineSizeBits = log2i(lineSize);

  nReadHit   = 0;
  nReadMiss  = 0;
  nWriteHit  = 0;
  nWriteMiss = 0;

  assert(getLineSize() < 4096); // To avoid bank selection conflict (insane LiveCache line)

  lineCount = (uint64_t)cacheBank->getNumLines();
  maxOrder  = 0;
}

LiveCache::~LiveCache() {

  if (nWriteMiss==0 && nWriteHit==0)
    nWriteMiss = 1;

  if (nReadMiss==0 && nReadHit==0)
    nReadMiss = 1;

  fprintf(stderr,"%s nReadHit:%lld nReadMiss:%lld nReadMissRate:%3.1f%% nWriteHit:%lld nWriteMiss:%lld nWriteMissRate:%3.1f%%\n"
      ,name.c_str()
      ,nReadHit
      ,nReadMiss
      ,100.0*((double)nReadMiss)/(nReadHit+nReadMiss)
      ,nWriteHit
      ,nWriteMiss
      ,100.0*((double)nWriteMiss)/(nWriteHit+nWriteMiss)
      );

  cacheBank->destroy();
}

void LiveCache::read(uint64_t addr) {
  Line *l = cacheBank->findLine(addr);
  if(l) {
    l->order = maxOrder++;
    nReadHit++;
    return;
  }
  nReadMiss++;

  l = cacheBank->fillLine(addr);
  l->st = false;
  l->order = maxOrder++;
}

void LiveCache::write(uint64_t addr) {
  Line *l = cacheBank->findLine(addr);
  if(l) {
    l->order = maxOrder++;
    l->st    = true;

    nWriteHit++;
    return;
  }
  nWriteMiss++;

  l = cacheBank->fillLine(addr);
  l->st = true;
  l->order = maxOrder++;
}

uint64_t *LiveCache::traverse(int &n_entries) {
  // Creating an array of cache lines
  Line *   arr[lineCount];
  uint64_t cnt = 0;
  for(uint64_t i = 0; i < lineCount; i++) {
    if(cacheBank->getPLine(i) && cacheBank->getPLine(i)->order) {
      arr[cnt] = cacheBank->getPLine(i);
      cnt++;
    }
  }
  mergeSort(arr, cnt);

  uint64_t *addrs = (uint64_t *)malloc(sizeof(uint64_t)*cnt);

  // creating loads and stores arrays
  uint64_t in = 0;
  for(uint64_t i = 0; i < cnt; i++) {
    if(!arr[i]->getTag())
      continue;
    if (arr[i]->st) {
      addrs[in] = 1 | (uint64_t)cacheBank->calcAddr4Tag(arr[i]->getTag());
    }else{
      addrs[in] = (uint64_t)cacheBank->calcAddr4Tag(arr[i]->getTag());
      assert((addrs[in]&1)==0);
    }
    in++;
  }

  n_entries = in;

  return addrs;
}

void LiveCache::mergeSort(Line **arr, uint64_t len) {
  // in case we had one element
  if(len < 2)
    return;

  // in case we had two elements
  if(len == 2) {
    if(arr[0]->order > arr[1]->order) {
      // swap
      Line *t = arr[0];
      arr[0]  = arr[1];
      arr[1]  = t;
    }
    return;
  }

  // divide and conquer
  uint64_t mid = (uint64_t)(len / 2);
  Line *   arr1[mid];
  Line *   arr2[len - mid];
  for(uint64_t i = 0; i < mid; i++)
    arr1[i] = arr[i];
  for(uint64_t i = 0; i < len - mid; i++)
    arr2[i] = arr[mid + i];
  mergeSort(arr1, mid);
  mergeSort(arr2, len - mid);

  // merging
  uint64_t m = 0;
  uint64_t n = 0;
  for(uint64_t i = 0; i < len; i++) {
    if(n >= (len - mid) || (m < mid && arr1[m]->order <= arr2[n]->order)) {
      arr[i] = arr1[m];
      m++;
    } else {
      arr[i] = arr2[n];
      n++;
    }
  }
}
