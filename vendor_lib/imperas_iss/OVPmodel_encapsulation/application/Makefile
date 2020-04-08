ifndef IMPERAS_HOME
  IMPERAS_ERROR := $(error "IMPERAS_HOME not defined, please setup Imperas/OVP environment")
endif
IMPERAS_HOME := $(shell getpath.exe "$(IMPERAS_HOME)")


all:
	# basic C applications
	$(MAKE) -C C_applications
	# google instruction stream generated test
	$(MAKE) -C google

clean:
	$(MAKE) -C C_applications clean
	$(MAKE) -C google         clean
	