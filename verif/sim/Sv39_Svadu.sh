# NUMBER OF TESTS : 20 (Sv39 | S-mode : 10 | U-mode : 10)

# TEST 0: Sv39 Svadu Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test total_test_Sv39_umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 1: Sv39 Svadu Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test total_test_Sv39_smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 2: Sv39 Level0 A-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV0_A_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 3: Sv39 Level0 D-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV0_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 4: Sv39 Level0 A/D-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV0_A_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 5: Sv39 Level1 A-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV1_A_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 6: Sv39 Level1 D-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV1_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 7: Sv39 Level1 A/D-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV1_A_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 8: Sv39 Level2 A-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV2_A_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 9: Sv39 Level2 D-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV2_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 10: Sv39 Level2 A/D-bit test Smode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV2_A_D_Smode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu


# TEST 11: Sv39 Level0 A-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV0_A_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 12: Sv39 Level0 D-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV0_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 13: Sv39 Level0 A/D-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV0_A_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 14: Sv39 Level1 A-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV1_A_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 15: Sv39 Level1 D-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV1_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 16: Sv39 Level1 A/D-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV1_A_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 17: Sv39 Level2 A-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV2_A_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu


# TEST 18: Sv39 Level2 D-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV2_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu

# TEST 19: Sv39 Level2 A/D-bit test Umode
python3 cva6.py --target cv64a6_imafdc_sv39_hpdcache \
--iss=spike,veri-testharness --iss_yaml=cva6.yaml \
--testlist=../tests/testlist_riscv-tests-Svadu.yaml \
--test Sv39_LV2_A_D_Umode \
--gcc_opts="-I/root/cva6/verif/tests/riscv-arch-test/riscv-target/spike -Wl,--defsym=_start=0x80000000 -DXLEN=64 -DTEST_CASE_1=True" \
--spike_extension=svadu