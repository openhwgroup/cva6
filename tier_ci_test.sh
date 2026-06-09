



DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a65x bash verif/regress/smoke-tests-cv32a65x.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a60x bash verif/regress/cv32a6_tests.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv64a6_imafdc_sv39_hpdcache_wb bash verif/regress/cv64a6_imafdc_tests.sh


DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a65x bash verif/regress/dv-riscv-arch-test.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a60x bash verif/regress/dv-riscv-arch-test.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv64a6_imafdc_sv39_hpdcache_wb bash verif/regress/dv-riscv-arch-test.sh




DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a65x DV_TESTLISTS=../tests/testlist_riscv-tests-cv32a65x-p.yaml bash verif/regress/dv-riscv-tests.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a60x DV_TESTLISTS=../tests/testlist_riscv-tests-cv32a60x-p.yaml bash verif/regress/dv-riscv-tests.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv64a6_imafdc_sv39 DV_TESTLISTS=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-p.yaml bash verif/regress/dv-riscv-tests.sh

DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv64a6_imafdc_sv39 DV_TESTLISTS=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-v.yaml bash verif/regress/dv-riscv-tests.sh

DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a65x bash verif/regress/dv-riscv-compliance.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv32a60x bash verif/regress/dv-riscv-compliance.sh
DV_SIMULATORS=veri-testharness,spike DV_TARGET=cv64a6_imafdc_sv39 bash verif/regress/dv-riscv-compliance.sh


DV_SIMULATORS=veri-testharness,spike bash verif/regress/dv-riscv-mmu-sv32-test.sh
