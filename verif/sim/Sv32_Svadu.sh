# NUMBER OF TESTS : 14 (Sv32 | S-mode : 7 | U-mode : 7)

# TEST 0: Sv32 Level0 A-bit test Smode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV0_A_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 1: Sv32 Level0 D-bit test Smode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV0_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 2: Sv32 Level0 A/D-bit test Smode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV0_A_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 3: Sv32 Level1 A-bit test Smode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV1_A_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 4: Sv32 Level1 D-bit test Smode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV1_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 5: Sv32 Level1 A/D-bit test Smode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV1_A_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 6: Sv32 Level0 A-bit test Umode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV0_A_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 7: Sv32 Level0 D-bit test Umode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV0_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 8: Sv32 Level0 A/D-bit test Umode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV0_A_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 9: Sv32 Level1 A-bit test Umode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV1_A_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 10: Sv32 Level1 D-bit test Umode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV1_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 11: Sv32 Level1 A/D-bit test Umode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv32_LV1_A_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 12: Sv32 Svadu Smode
python3 cva6.py --target cv32a6_imac_sv32 \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test total_test_Sv32_smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 13: Sv32 Svadu Umode32
python3 cva6.py --target cv32a6_imac_sv32 --iss=spike,veri-testharness \
--iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test total_test_Sv32_umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=32 -DTEST_CASE_1=True" \
--spike_extension=svadu