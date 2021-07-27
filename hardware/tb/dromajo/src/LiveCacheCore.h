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
// Contributed by Jose Renau
//                Basilio Fraguela
//                James Tuck
//                Milos Prvulovic
//                Smruti Sarangi
//
// The ESESC/BSD License
//
// Copyright (c) 2005-2013, Regents of the University of California and
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

#ifndef LIVECACHECORE_H
#define LIVECACHECORE_H

#include <vector>

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include <strings.h>

//-------------------------------------------------------------
#define RRIP_M       4 // max value = 2^M   | 4 | 8   | 16   |
//-------------------------------------------------------------
#define DISTANT_REF  3 // 2^M - 1           | 3 | 7   | 15   |
#define IMM_REF      1 // nearimm<imm<dist  | 1 | 1-6 | 1-14 |
#define NEAR_IMM_REF 0 // 0                 | 0 | 0   | 0    |
#define LONG_REF     1 // 2^M - 2           | 1 | 6   | 14   |
//-------------------------------------------------------------

static inline uint32_t roundUpPower2(uint32_t x) {
  // efficient branchless code extracted from "Hacker's Delight" by
  // Henry S. Warren, Jr.

  x = x - 1;
  x = x | (x >> 1);
  x = x | (x >> 2);
  x = x | (x >> 4);
  x = x | (x >> 8);
  x = x | (x >> 16);
  return x + 1;
}

static inline short log2i(uint32_t n) {
  uint32_t m = 1;
  uint32_t i = 0;

  if(n == 1)
    return 0;

  n = roundUpPower2(n);
  // assume integer power of 2
  assert((n & (n - 1)) == 0);

  while(m < n) {
    i++;
    m <<= 1;
  }

  return i;
}

enum ReplacementPolicy { LRU, LRUp, RANDOM};

template<class State, class Addr_t> class CacheGeneric {
private:
  static const int32_t STR_BUF_SIZE = 1024;

protected:
  const uint32_t size;
  const uint32_t lineSize;
  const uint32_t assoc;
  const uint32_t log2Assoc;
  const uint64_t log2AddrLs;
  const uint64_t maskAssoc;
  const uint32_t sets;
  const uint32_t maskSets;
  const uint32_t log2Sets;
  const uint32_t numLines;

  const bool xorIndex;

  bool goodInterface;

public:
  class CacheLine : public State {
  public:
    CacheLine() {
    }
    // Pure virtual class defines interface
    //
    // Tag included in state. Accessed through:
    //
    // Addr_t getTag() const;
    // void setTag(Addr_t a);
    // void clearTag();
    //
    //
    // bool isValid() const;
    // void invalidate();
  };

  // findLine returns a cache line that has tag == addr, NULL otherwise
  virtual CacheLine *findLinePrivate(Addr_t addr) = 0;

protected:
  CacheGeneric(uint32_t s, uint32_t a, uint32_t b, bool xr)
      : size(s)
      , lineSize(b)
      , assoc(a)
      , log2Assoc(log2i(a))
      , log2AddrLs(log2i(b))
      , maskAssoc(a - 1)
      , sets((s / b) / a)
      , maskSets(sets - 1)
      , log2Sets(log2i(sets))
      , numLines(s / b)
      , xorIndex(xr) {
    // TODO : assoc and sets must be a power of 2
  }

  virtual ~CacheGeneric() {
  }

public:
  // Do not use this interface, use other create
  static CacheGeneric<State, Addr_t> *create(int32_t size, int32_t assoc, int32_t blksize, const char *pStr,
                                             bool xr);
  void                                destroy() {
    delete this;
  }

  virtual CacheLine *findLine2Replace(Addr_t addr) = 0;

  // TO DELETE if flush from Cache.cpp is cleared.  At least it should have a
  // cleaner interface so that Cache.cpp does not touch the internals.
  //
  // Access the line directly without checking TAG
  virtual CacheLine *getPLine(uint32_t l) = 0;

  // ALL USERS OF THIS CLASS PLEASE READ:
  //
  // readLine and writeLine MUST have the same functionality as findLine. The only
  // difference is that readLine and writeLine update power consumption
  // statistics. So, only use these functions when you want to model a physical
  // read or write operation.

  // Use this is for debug checks. Otherwise, a bad interface can be detected

  CacheLine *findLineDebug(Addr_t addr) {
    IS(goodInterface = true);
    CacheLine *line = findLine(addr);
    IS(goodInterface = false);
    return line;
  }

  CacheLine *findLineNoEffect(Addr_t addr) {
    IS(goodInterface = true);
    CacheLine *line = findLine(addr);
    IS(goodInterface = false);
    return line;
  }

  CacheLine *findLine(Addr_t addr) {
    return findLinePrivate(addr);
  }

  CacheLine *readLine(Addr_t addr) {

    IS(goodInterface = true);
    CacheLine *line = findLine(addr);
    IS(goodInterface = false);

    return line;
  }

  CacheLine *writeLine(Addr_t addr) {

    IS(goodInterface = true);
    CacheLine *line = findLine(addr);
    IS(goodInterface = false);

    return line;
  }

  CacheLine *fillLine(Addr_t addr) {
    CacheLine *l = findLine2Replace(addr);
    assert(l);
    l->setTag(calcTag(addr));

    return l;
  }

  CacheLine *fillLine(Addr_t addr, Addr_t &rplcAddr) {
    CacheLine *l = findLine2Replace(addr);
    assert(l);
    rplcAddr = 0;

    Addr_t newTag = calcTag(addr);
    if(l->isValid()) {
      Addr_t curTag = l->getTag();
      if(curTag != newTag) {
        rplcAddr = calcAddr4Tag(curTag);
      }
    }

    l->setTag(newTag);

    return l;
  }

  uint32_t getLineSize() const {
    return lineSize;
  }
  uint32_t getAssoc() const {
    return assoc;
  }
  uint32_t getLog2AddrLs() const {
    return log2AddrLs;
  }
  uint32_t getLog2Assoc() const {
    return log2Assoc;
  }
  uint32_t getMaskSets() const {
    return maskSets;
  }
  uint32_t getNumLines() const {
    return numLines;
  }
  uint32_t getNumSets() const {
    return sets;
  }

  Addr_t calcTag(Addr_t addr) const {
    return (addr >> log2AddrLs);
  }

  // Addr_t calcSet4Tag(Addr_t tag)     const { return (tag & maskSets);                  }
  // Addr_t calcSet4Addr(Addr_t addr)   const { return calcSet4Tag(calcTag(addr));        }

  // Addr_t calcIndex4Set(Addr_t set) const { return (set << log2Assoc);                }
  // Addr_t calcIndex4Tag(Addr_t tag) const { return calcIndex4Set(calcSet4Tag(tag));   }
  // uint32_t calcIndex4Addr(Addr_t addr) const { return calcIndex4Set(calcSet4Addr(addr)); }
  Addr_t calcIndex4Tag(Addr_t tag) const {
    Addr_t set;
    if(xorIndex) {
      tag = tag ^ (tag >> log2Sets);
      // Addr_t odd = (tag&1) | ((tag>>2) & 1) | ((tag>>4)&1) | ((tag>>6)&1) | ((tag>>8)&1) | ((tag>>10)&1) | ((tag>>12)&1) |
      // ((tag>>14)&1) | ((tag>>16)&1) | ((tag>>18)&1) | ((tag>>20)&1); // over 20 bit index???
      set = tag & maskSets;
    } else {
      set = tag & maskSets;
    }
    Addr_t index = set << log2Assoc;
    return index;
  }

  Addr_t calcAddr4Tag(Addr_t tag) const {
    return (tag << log2AddrLs);
  }
};


template <class State, class Addr_t> class CacheAssoc : public CacheGeneric<State, Addr_t> {
  using CacheGeneric<State, Addr_t>::numLines;
  using CacheGeneric<State, Addr_t>::assoc;
  using CacheGeneric<State, Addr_t>::maskAssoc;
  using CacheGeneric<State, Addr_t>::goodInterface;

private:
public:
  typedef typename CacheGeneric<State, Addr_t>::CacheLine Line;

protected:
  Line  *mem;
  Line **content;
  uint16_t          irand;
  ReplacementPolicy policy;

  friend class CacheGeneric<State, Addr_t>;
  CacheAssoc(int32_t size, int32_t assoc, int32_t blksize, const char *pStr, bool xr);

  Line *findLinePrivate(Addr_t addr);

public:
  virtual ~CacheAssoc() {
  }

  // TODO: do an iterator. not this junk!!
  Line *getPLine(uint32_t l) {
    // Lines [l..l+assoc] belong to the same set
    assert(l < numLines);
    return content[l];
  }

  Line *findLine2Replace(Addr_t addr);
};

template <class State, class Addr_t> class CacheDM : public CacheGeneric<State, Addr_t> {
  using CacheGeneric<State, Addr_t>::numLines;
  using CacheGeneric<State, Addr_t>::goodInterface;

private:
public:
  typedef typename CacheGeneric<State, Addr_t>::CacheLine Line;

protected:
  Line  *mem;
  Line **content;

  friend class CacheGeneric<State, Addr_t>;
  CacheDM(int32_t size, int32_t blksize, const char *pStr, bool xr);

  Line *findLinePrivate(Addr_t addr);

public:
  virtual ~CacheDM() {
  };

  // TODO: do an iterator. not this junk!!
  Line *getPLine(uint32_t l) {
    // Lines [l..l+assoc] belong to the same set
    assert(l < numLines);
    return content[l];
  }

  Line *findLine2Replace(Addr_t addr);
};

template <class Addr_t> class StateGeneric {
private:
  Addr_t tag;

public:
  virtual ~StateGeneric() {
    tag = 0;
  }

  Addr_t getTag() const {
    return tag;
  }
  void setTag(Addr_t a) {
    assert(a);
    tag = a;
  }
  void clearTag() {
    tag = 0;
  }
  void initialize(void *c) {
    clearTag();
  }

  virtual bool isValid() const {
    return tag;
  }

  virtual void invalidate() {
    clearTag();
  }

  virtual void dump(const char *str) {
  }

  Addr_t getSignature() const {
    return 0;
  }
  void setSignature(Addr_t a) {
    assert(0);
  }
  bool getOutcome() const {
    return 0;
  }
  void setOutcome(bool a) {
    assert(0);
  }
  uint8_t getRRPV() const {
    return 0;
  }

  void setRRPV(uint8_t a) {
    assert(0);
  }

  void incRRPV() {
    assert(0);
  }
};

#include "LiveCache.h"

#define k_RANDOM "RANDOM"
#define k_LRU "LRU"
#define k_LRUp "LRUp"

//
// Class CacheGeneric, the combinational logic of Cache
//
template <class State, class Addr_t>
CacheGeneric<State, Addr_t> *CacheGeneric<State, Addr_t>::create(int32_t size, int32_t assoc, int32_t bsize,
                                                                 const char *pStr, bool xr) {
  CacheGeneric *cache;

  if(assoc == 1) {
    cache = new CacheDM<State, Addr_t>(size, bsize, pStr, xr);
  } else {
    cache = new CacheAssoc<State, Addr_t>(size, assoc, bsize, pStr, xr);
  }

  assert(cache);
  return cache;
}

/*********************************************************
 *  CacheAssoc
 *********************************************************/

template <class State, class Addr_t>
CacheAssoc<State, Addr_t>::CacheAssoc(int32_t size, int32_t assoc, int32_t blksize, const char *pStr, bool xr)
    : CacheGeneric<State, Addr_t>(size, assoc, blksize, xr) {
  assert(numLines > 0);

  assert((int32_t)numLines > assoc);

  if(strcasecmp(pStr, k_RANDOM) == 0)
    policy = RANDOM;
  else if(strcasecmp(pStr, k_LRU) == 0)
    policy = LRU;
  else if(strcasecmp(pStr, k_LRUp) == 0)
    policy = LRUp;
  else {
    fprintf(stderr,"Invalid cache policy [%s]\n", pStr);
    exit(0);
  }

  mem = (Line *)malloc(sizeof(Line) * (numLines + 1));
  for(uint32_t i = 0; i < numLines; i++) {
    new (&mem[i]) Line;
  }
  content = new Line *[numLines + 1];

  for(uint32_t i = 0; i < numLines; i++) {
    mem[i].initialize(this);
    mem[i].invalidate();
    content[i] = &mem[i];
  }

  irand = 0;
}

template <class State, class Addr_t>
typename CacheAssoc<State, Addr_t>::Line *CacheAssoc<State, Addr_t>::findLinePrivate(Addr_t addr) {
  Addr_t tag = this->calcTag(addr);

  Line **theSet = &content[this->calcIndex4Tag(tag)];

  // Check most typical case
  if((*theSet)->getTag() == tag) {
    return *theSet;
  }

  Line **lineHit = 0;
  Line **setEnd  = theSet + assoc;

  // For sure that position 0 is not (short-cut)
  {
    Line **l = theSet + 1;
    while(l < setEnd) {
      if((*l)->getTag() == tag) {
        lineHit = l;
        break;
      }
      l++;
    }
  }

  if(lineHit == 0)
    return 0;

  Line *tmp = *lineHit;
  {
    Line **l = lineHit;
    while(l > theSet) {
      Line **prev = l - 1;
      *l          = *prev;
      ;
      l = prev;
    }
    *theSet = tmp;
  }

  return tmp;
}

template <class State, class Addr_t>
typename CacheAssoc<State, Addr_t>::Line *CacheAssoc<State, Addr_t>::findLine2Replace(Addr_t addr) {
  Addr_t tag = this->calcTag(addr);
  assert(tag);
  Line **theSet = &content[this->calcIndex4Tag(tag)];

  // Check most typical case
  if((*theSet)->getTag() == tag) {
    // GI(tag,(*theSet)->isValid()); //TODO: why is this assertion failing
    return *theSet;
  }

  Line **lineHit  = 0;
  Line **lineFree = 0; // Order of preference, invalid
  Line **setEnd   = theSet + assoc;

  {
    Line **l = setEnd - 1;
    while(l >= theSet) {
      if((*l)->getTag() == tag) {
        lineHit = l;
        break;
      }
      if(!(*l)->isValid())
        lineFree = l;
      else if(lineFree == 0)
        lineFree = l;

      l--;
    }
  }

  Line * tmp;
  Line **tmp_pos;
  if(!lineHit) {

    assert(lineFree);

    if(policy == RANDOM) {
      lineFree = &theSet[irand];
      irand    = (irand + 1) & maskAssoc;
      if(irand == 0)
        irand = (irand + 1) & maskAssoc; // Not MRU
    } else {
      assert(policy == LRU || policy == LRUp);
      // Get the oldest line possible
      lineFree = setEnd - 1;
    }

    assert(lineFree);

    if(lineFree == theSet)
      return *lineFree; // Hit in the first possition

    tmp     = *lineFree;
    tmp_pos = lineFree;
  } else {
    tmp     = *lineHit;
    tmp_pos = lineHit;
  }

  if(policy == LRUp) {
#if 0
    Line **l = tmp_pos;
    while(l > &theSet[13]) {
      Line **prev = l - 1;
      *l = *prev;;
      l = prev;
    }
    theSet[13] = tmp;
#endif
  } else {
    Line **l = tmp_pos;
    while(l > theSet) {
      Line **prev = l - 1;
      *l          = *prev;
      ;
      l = prev;
    }
    *theSet = tmp;
  }

  return tmp;
}

/*********************************************************
 *  CacheDM
 *********************************************************/

template <class State, class Addr_t>
CacheDM<State, Addr_t>::CacheDM(int32_t size, int32_t blksize, const char *pStr, bool xr)
    : CacheGeneric<State, Addr_t>(size, 1, blksize, xr) {
  assert(numLines > 0);

  mem = (Line *)malloc(sizeof(Line) * (numLines + 1));
  for(uint32_t i = 0; i < numLines; i++) {
    new (&mem[i]) Line;
  }
  content = new Line *[numLines + 1];

  for(uint32_t i = 0; i < numLines; i++) {
    mem[i].initialize(this);
    mem[i].invalidate();
    content[i] = &mem[i];
  }
}

template <class State, class Addr_t>
typename CacheDM<State, Addr_t>::Line *CacheDM<State, Addr_t>::findLinePrivate(Addr_t addr) {
  Addr_t tag = this->calcTag(addr);
  assert(tag);

  Line *line = content[this->calcIndex4Tag(tag)];

  if(line->getTag() == tag) {
    assert(line->isValid());
    return line;
  }

  return 0;
}

template <class State, class Addr_t>
typename CacheDM<State, Addr_t>::Line *CacheDM<State, Addr_t>::findLine2Replace(Addr_t addr) {
  Addr_t tag  = this->calcTag(addr);
  Line * line = content[this->calcIndex4Tag(tag)];

  return line;
}

#endif // LIVECACHECORE_H
