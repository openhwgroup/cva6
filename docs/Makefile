all: prepare sphinx

prepare:
	make -C 04_cv32a65x/riscv priv-html unpriv-html
	make -C 04_cv32a65x/design design-html

	make -C 06_cv64a6_mmu/riscv priv-html unpriv-html

sphinx:
	sphinx-build . _build

.PHONY: all prepare sphinx
