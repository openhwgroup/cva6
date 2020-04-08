ifndef IMPERAS_HOME
  IMPERAS_ERROR := $(error "IMPERAS_HOME not defined, please setup Imperas/OVP environment")
endif
IMPERAS_HOME := $(shell getpath.exe "$(IMPERAS_HOME)")

# Default to compile locally
NOVLNV?=1
# Build to a shared object
HARNESSLIB=1
# Name of source
SRC?=riscv_sv.c
include $(IMPERAS_HOME)/ImperasLib/buildutils/Makefile.harness
