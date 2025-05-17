HPDCACHE_DIR = ../..
RM = rm -f

export HPDCACHE_DIR

HPDCACHE_FILES=$(shell grep '.*.sv' $(HPDCACHE_DIR)/rtl/hpdcache.Flist)

.PHONY: verilator-lint verible-lint all

verilator-lint:
	verilator --cc \
		-Wall \
		-Wno-pinconnectempty \
		-Wno-fatal \
		-error-limit 100 \
		--top hpdcache_lint \
		-f $(HPDCACHE_DIR)/rtl/hpdcache.Flist \
		$(HPDCACHE_DIR)/rtl/src/common/macros/behav/*.sv \
		hpdcache_lint.sv

verible-lint:
	verible-verilog-lint \
		--rules_config verible_rules.cfg \
		--waiver_files verible.waiver \
		$(HPDCACHE_FILES) \
		$(HPDCACHE_DIR)/rtl/src/common/macros/behav/*.sv \
		hpdcache_lint.sv

all: verilator-lint verible-lint

.PHONY: clean
clean:
	$(RM) -r obj_dir
