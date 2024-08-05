all: prepare sphinx

prepare:
	python3 scripts/spec_builder.py 04_cv32a65x
	make -C 04_cv32a65x/riscv priv-html unpriv-html
	make -C 04_cv32a65x/design design-html

	python3 scripts/spec_builder.py 06_cv64a6_mmu
	make -C 06_cv64a6_mmu/riscv priv-html unpriv-html

sphinx:
	sphinx-build . _build

.PHONY: all prepare sphinx
