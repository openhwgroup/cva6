#   Copyright 2024 Thales DIS France SAS
#   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#   You may obtain a copy of the License at https://solderpad.org/licenses/
#
#   Original Author: Jean-Roch COULON - Thales

# Build Targets
TARGETS_PDF := design.pdf
TARGETS_HTML := design.html
TARGETS_EPUB := design.epub
TARGETS := $(TARGETS_PDF) $(TARGETS_HTML) $(TARGETS_EPUB)

SHORT_TARGETS := design-pdf design-html design-epub

# Declare phony targets
.PHONY: all docker clean $(SHORT_TARGETS)

# Default target builds all
all: $(TARGETS)

define run_with_docker
	cd .. && docker run -it -v `pwd`:/build riscvintl/riscv-docs-base-container-image:latest /bin/sh -c 'export LANG=C.utf8; cd ./build; $(1)'
endef

# Run natively if command exists, otherwise run with docker
define maybe_run_with_docker
	@if command -v $(1) &> /dev/null; \
	then \
		$(1) $(2); \
	else \
		$(call run_with_docker, $(1) $(2)); \
	fi
endef

docker:
	$(call run_with_docker, make -$(MAKEFLAGS) all)

# Asciidoctor options
ASCIIDOCTOR_OPTS := -a compress \
                    --attribute=mathematical-format=svg \
                    --failure-level=ERROR \
                    --require=asciidoctor-diagram \
                    --require=asciidoctor-mathematical \
                    --trace

# Source directory
SRCDIR := ../source_adoc
IMGSDIR:= ../images
ALL_SRCS := $(shell find $(SRCDIR) -type f -name \"*.adoc\") $(shell find $(IMGSDIR) -type f)

# Design Documentation build
design-pdf: design.pdf

design.pdf: $(SRCDIR)/design.adoc $(ALL_SRCS)
	@echo "Building Design Documentation PDF"
	@rm -f $@.tmp
	$(call maybe_run_with_docker, asciidoctor-pdf, $(ASCIIDOCTOR_OPTS) --out-file=$@.tmp $<)
	@mv $@.tmp $@

# Design Documentation HTML build
design-html: design.html

design.html: $(SRCDIR)/design.adoc $(ALL_SRCS)
	@echo "Building Design Documentation  HTML"
	@rm -f $@.tmp
	$(call maybe_run_with_docker, asciidoctor, $(ASCIIDOCTOR_OPTS) --out-file=$@.tmp $<)
	@mv $@.tmp $@

# Design Documentation epub build
design-epub: design.epub

design.epub: $(SRCDIR)/design.adoc $(ALL_SRCS)
	@echo "Building Design Documentation EPUB"
	@rm -f $@.tmp
	$(call maybe_run_with_docker, asciidoctor-epub3, $(ASCIIDOCTOR_OPTS) --out-file=$@.tmp $<)
	@mv $@.tmp $@

clean:
	rm -f $(TARGETS) $(addsuffix .tmp,$(TARGETS))
