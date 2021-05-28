TARGETS = $(filter-out common/.,$(wildcard */.))

.PHONY: all ${TARGETS}
all: ${TARGETS}

${TARGETS}:
	$(MAKE) -C $@
