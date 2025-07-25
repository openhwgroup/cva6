CC = g++
INC ?= $(HOME)/runtime_adept/digilent.adept.sdk_2.4.2
LIBDIR = /usr/lib64/digilent/adept
TARGETS = Receiver_DPTI
CFLAGS = -I $(INC) -L $(LIBDIR) -ldpti -ldmgr -Wall -Wextra -g

all: $(TARGETS)

Receiver_DPTI: Receiver_DPTI.cpp
	$(CC) -o Receiver_DPTI Receiver_DPTI.cpp $(CFLAGS)

.PHONY: clean

clean:
	rm -f $(TARGETS)

clean_all:
	rm -f $(TARGETS)
	rm -rf receiver_data
