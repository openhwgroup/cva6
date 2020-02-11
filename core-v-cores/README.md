## CORE-V-CORES
One or more CORE-V cores are cloned to this directory by the verification
Makefiles.  For example you will see something like this in the simulation
Makefiles:
```
# RTL dependencies
CV32E40P_HOME   := $(ROOT)/core-v-cores/cv32e40p
CV32E40P_RTLSRC := $(CV32E40P_HOME)/rtl 

# Rule to fetch the latest RTL for CV32E40P
$(CV32E40P_RTLSRC):
	git clone https://github.com/openhwgroup/core-v-verif --recurse $(CV32E40P_RTLSRC)
```
The structure supports multiple CORE-V cores being used in the same working copy
of CORE-V-VERIF.  For example we could have
`CV64A_HOME := $(ROOT)/core-v-cores/cv64a` and this would not conflict with CV32E.
