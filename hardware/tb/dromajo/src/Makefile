#
# Dromajo, a RISC-V Emulator (based on Fabrice Bellard's RISCVEMU/TinyEMU)
#
# Copyright (c) 2016-2017 Fabrice Bellard
# Copyright (c) 2018,2019 Esperanto Technology
#
# Licensed under the Apache License, Version 2.0 (the "License")
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# THIS FILE IS BASED ON RISCVEMU SOURCE CODE WHICH IS DISTRIBUTED UNDER
# THE FOLLOWING LICENSE:
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
#

VERSION=Dromajo-0.1

CXX=g++
CFLAGS_OPT=-Ofast
CXXFLAGS=$(CFLAGS_OPT) -Wall -std=c++11 -g -Wno-parentheses -D_FILE_OFFSET_BITS=64 -D_LARGEFILE_SOURCE -MMD
CXXFLAGS+=-D_GNU_SOURCE -DCONFIG_VERSION=\"$(VERSION)\"
#CXXFLAGS+=-DLIVECACHE
LDFLAGS=

bindir=/usr/local/bin
INSTALL=install
PROGS=dromajo libdromajo_cosim.a

all: $(PROGS)

EMU_OBJS:=virtio.o pci.o fs.o cutils.o iomem.o dw_apb_uart.o \
    json.o machine.o elf64.o LiveCache.o fs_disk.o

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	CXXFLAGS += -Werror
	EMU_LIBS=-lrt
endif
ifeq ($(UNAME_S),Darwin)
	EMU_LIBS=
endif

dromajo: dromajo.o libdromajo_cosim.a
	$(CXX) $(LDFLAGS) -o $@ $^ $(DROMAJO_LIBS) $(EMU_LIBS)

dromajo_cosim_test: dromajo_cosim_test.o libdromajo_cosim.a
	$(CXX) $(LDFLAGS) -o $@ $^ $(DROMAJO_LIBS) $(EMU_LIBS)

libdromajo_cosim.a: dromajo_cosim.o riscv_cpu.o dromajo_main.o \
	riscv_machine.o softfp.o $(EMU_OBJS)
	ar rvs $@ $^

install: $(PROGS)
	$(INSTALL) -m755 $(PROGS) "$(DESTDIR)$(bindir)"

%.o: %.c
	$(CXX) $(CXXFLAGS) -c -o $@ $<

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c -o $@ $<

debug:
	$(MAKE) CFLAGS_OPT=

build:
	mkdir -p build

clean:
	rm -f *.o *.d *~ $(PROGS)
	rm -rf build

-include $(wildcard *.d)

tags:
	etags *.[hc]

release:
	git archive HEAD | xz -9 > dromajo-$(shell date +%Y%m%d)-$(shell git rev-parse --short HEAD).tar.xz
	git tag release-$(shell date +%Y%m%d)
