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

#ifndef LiveCache_H
#define LiveCache_H

#include <stdint.h>
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>

#include <string>

class LiveCache {
protected:
  class CState : public StateGeneric<uint64_t> {
  private:
    enum StateType { M, E, S, I };
    StateType state;

  public:
    bool     st;
    uint64_t order;

    CState() {
      state = I;
      clearTag();
    }

    bool isModified() const {
      return state == M;
    }
    void setModified() {
      state = M;
    }
    bool isValid() const {
      return state != I;
    }
    bool isInvalid() const {
      return state == I;
    }

    StateType getState() const {
      return state;
    };

    void invalidate() {
      state = I;
    }
  };

  typedef CacheGeneric<CState, uint64_t>            CacheType;
  typedef CacheGeneric<CState, uint64_t>::CacheLine Line;

  const std::string name;

  CacheType *cacheBank;

  int32_t  lineSize;
  int32_t  lineSizeBits;
  uint64_t lineCount;
  uint64_t maxOrder;

  long long  nReadHit;
  long long  nReadMiss;
  long long  nWriteHit;
  long long  nWriteMiss;

  void mergeSort(Line **arr, uint64_t len);

public:
  LiveCache(const std::string &_name, int size);
  virtual ~LiveCache();

  int32_t getLineSize() const {
    return lineSize;
  }

  void     read(uint64_t addr);
  void     write(uint64_t addr);
  uint64_t *traverse(int &n_entries);
};

#endif
