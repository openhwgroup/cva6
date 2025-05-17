##
##  Copyright 2023 CEA*
##  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
##
##  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
##
##  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
##  may not use this file except in compliance with the License, or, at your
##  option, the Apache License version 2.0. You may obtain a copy of the
##  License at
##
##  https://solderpad.org/licenses/SHL-2.1/
##
##  Unless required by applicable law or agreed to in writing, any work
##  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
##  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
##  License for the specific language governing permissions and limitations
##  under the License.
##
##  Author(s):          Cesar Fuguet
##  Date:               February, 2023
##  Description:        Makefile for the specification document of the HPDcache
##                      hardware IP
##
LATEXMK       = latexmk -pdf
INKSCAPE      = inkscape --without-gui
PDFVIEWER     = evince
RM            = rm -rf
RMDIR         = rmdir -p
CP            = cp -f
ECHO          = echo -e
MKDIR         = mkdir -p

PDF_DIR       = pdf
AUX_DIR       = build
SOURCE_DIR    = source
RELEASE_DIR   = release

VERSION       = $(shell cat version)

TARGET        = hpdcache_spec
TEX_SOURCES   = $(SOURCE_DIR)/$(TARGET).bib \
                $(SOURCE_DIR)/hpdcache_spec_changelog.tex \
                $(SOURCE_DIR)/hpdcache_spec_preamble.tex \
                $(AUX_DIR)/hpdcache_data_ram_organization.pdf \
                $(AUX_DIR)/hpdcache_request_arbiter.pdf \
                $(AUX_DIR)/hpdcache_core.pdf \
                $(AUX_DIR)/hpdcache_request_address_data_alignment.pdf \
                $(AUX_DIR)/hpdcache_data_ram_organization.emf \
                $(AUX_DIR)/hpdcache_request_arbiter.emf \
                $(AUX_DIR)/hpdcache_core.emf \
                $(AUX_DIR)/hpdcache_request_address_data_alignment.emf \
                $(AUX_DIR)/wave_ready_before_valid.pdf \
                $(AUX_DIR)/wave_valid_before_ready.pdf \
                $(AUX_DIR)/wave_ready_when_valid.pdf \
                $(AUX_DIR)/wave_back_to_back.pdf \
                $(AUX_DIR)/wave_ready_before_valid.emf \
                $(AUX_DIR)/wave_valid_before_ready.emf \
                $(AUX_DIR)/wave_ready_when_valid.emf \
                $(AUX_DIR)/wave_back_to_back.emf

LATEXMK_ARGS  = -bibtex \
                $(if $(VERBOSE),,-silent) \
                -pretex='\newcommand{\docversion}{$(VERSION)}' \
                -usepretex

vpath %.svg $(SOURCE_DIR)/images
vpath %.svg $(SOURCE_DIR)/images/exported

all:
	@$(ECHO) "usage: make [target]\n"
	@$(ECHO) "Target candidates:\n"
	@$(ECHO) "pdf                            generate PDF document"
	@$(ECHO) "release                        make a release of the PDF document"
	@$(ECHO) "view                           view PDF document"
	@$(ECHO) "clean                          clean auxiliary files"
	@$(ECHO) "clean_pdf                      clean PDF file"
	@$(ECHO) "distclean                      clean all generated files"

.PHONY: release
release: $(RELEASE_DIR)/$(TARGET)-$(VERSION).pdf

$(RELEASE_DIR)/$(TARGET)-$(VERSION).pdf: $(PDF_DIR)/$(TARGET).pdf
	@$(MKDIR) $(dir $@)
	$(CP) $< $@

.PHONY: pdf
pdf: $(PDF_DIR)/$(TARGET).pdf

$(PDF_DIR)/$(TARGET).pdf: $(AUX_DIR)/$(TARGET).pdf
	@$(MKDIR) $(dir $@)
	$(CP) $< $@

$(AUX_DIR)/$(TARGET).pdf: $(SOURCE_DIR)/$(TARGET).tex \
                          $(TEX_SOURCES)
	@$(MKDIR) $(dir $@)
	$(LATEXMK) $(LATEXMK_ARGS) --output-directory=$(dir $@) $<

$(AUX_DIR)/%.pdf: %.svg
	@$(MKDIR) $(dir $@)
	$(INKSCAPE) --export-pdf=$@ --export-area-drawing $<

$(AUX_DIR)/%.emf: %.svg
	@$(MKDIR) $(dir $@)
	$(INKSCAPE) --export-emf=$@ --export-area-drawing $<

.PHONY: view
view: $(PDF_DIR)/$(TARGET).pdf
	@$(ECHO) "Opening PDF viewer..."
	@$(PDFVIEWER) $< >&/dev/null &

.PHONY: clean clean_pdf distclean
clean:
	@$(ECHO) "Cleaning build directory..."
	@$(RM) $(AUX_DIR)

clean_pdf:
	@$(ECHO) "Cleaning generated PDF file..."
	@$(RM) $(PDF_DIR)/$(TARGET).pdf
	@$(RMDIR) $(PDF_DIR) >&/dev/null || true

distclean: clean clean_pdf
