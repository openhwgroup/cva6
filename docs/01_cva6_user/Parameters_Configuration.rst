..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales DIS design services SAS

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_parameters_configuration:

Parameters and Configuration
============================

Main contributor: Jean-Roch Coulon - Thales


Parameters
----------

.. csv-table::
   :widths: auto
   :align: left
   :header: "Parameter", "Category", "Description"

   "``Cva6MArchID``",               "Archi",            "Cva6 architecture ID"
   "``Xlen``",                      "Variant",          "Data length"
   "``CExtEn``",                    "Variant",          "C extension enable"
   "``AExtEn``",                    "Variant",          "A extension enable"
   "``BMExtEn``",                   "Variant",          "Bit Manipulation extension enable"
   "``FpuEn``",                     "Variant",          "FPU enable"
   "``F16En``",                     "Variant",          "FPU 16bits enable"
   "``F16AltEn``",                  "Variant",          "FPU Alt 16bits enable"
   "``F8En``",                      "Variant",          "FPU 8bits enable"
   "``FVecEn``",                    "Variant",          "Vector FPU enable"
   "``MMUEn``",                     "Memory",           "MMU Present"
   "``InstrTlbEntries``",           "Memory",           "Instruction TLB entry number"
   "``DataTlbEntries``",            "Memory",           "Data TLB entry number"
   "``RASDepth``",                  "Memory",           "Depth of Return Address Stack"
   "``BTBEntries``",                "Memory",           "BTB entry number"
   "``BHTEntries``",                "Memory",           "BHT entry number"
   "``NrNonIdempotentRules``",      "Memory",           "Number of non idempotent region"
   "``NonIdempotentAddrBase``",     "Memory",           "Base address of non idempotent region"
   "``NonIdempotentLength``",       "Memory",           "Length of non idempotent region"
   "``NrExecuteRegionRules``",      "Memory",           "Number of excution regions"
   "``ExecuteRegionAddrBase``",     "Memory",           "Execution region of base address (DRAM, Boot ROM and Debug Module)"
   "``ExecuteRegionLength``",       "Memory",           "Length of execution region"
   "``NrCachedRegionRules``",       "Memory",           "Number of cached region"
   "``CachedRegionAddrBase``",      "Memory",           "Base address of cached region"
   "``CachedRegionLength``",        "Memory",           "Length of cached regions"
   "``NrPMPEntries``",              "Memory",           "Number of PMP entries"
   "``DmBaseAddress``",             "Debug",            "Base address of debug"
   "``CvxifEn``",                   "Ports",            "CV-X-IF interface enable"
   "``RVFI_TRACE (define)``",       "Ports",            "RVFI interface enable"
   "``FIRESIM_TRACE (define)``",    "Ports",            "FIRESIM interface enable"
   "``PITON_ARIANE (define)``",     "Ports",            "Piton interface enable, and AXI interface disable"
   "``WT_CACHE (define)``",         "Caches",           "Write through cache enable, write back cache disable"
   "``DepthStoreBuffer``",          "Caches",           "Depth of store buffer"
   "``IcacheSetAssoc``",            "Caches",           "Instruction cache way number"
   "``DcacheSetAssoc``",            "Caches",           "Data cache way number"
   "``NrLoadPipeRegs``",            "Caches",           "Number of stall on load operation"
   "``NrStorePipeRegs``",           "Caches",           "Number of stall on store operation"
   "``AxiCompliant``",              "Caches",           "Cache configuration: AXI or XXXX"
   "``SwapEndianess``",             "Caches",           "Endianess of cache: XXXX"
   "``FetchUserEn``",               "Users",            "Fetch AXI user bit enable"
   "``FetchUserWidth``",            "Users",            "Fetch user bit number when enabled"
   "``DataUserEn``",                "Users",            "Data AXI user bit enable"
   "``DataUserWidth``",             "Users",            "Data user bit number when enabled"
   "``RenameEn``",                  "Pipeline",         "Register renaming feature enable"
   "``NrCommitPorts``",             "Pipeline",         "Commit port number"
   "``NrScoreboardEntries``",       "Pipeline",         "Scoreboard entry number"
   "``FpgaEn``",                    "Technology",       "FPGA optimization enable"


Configurations
--------------
A configuration is a fixed set of parameters.

.. csv-table::
   :widths: auto
   :align: left
   :header: "Parameter", "CV32A6_v5.0.0 config"

   "``Cva6MArchID``",               "3"
   "``Xlen``",                      "32"
   "``CExtEn``",                    "1"
   "``AExtEn``",                    "1"
   "``BMExtEn``",                   "0"
   "``FpuEn``",                     "0"
   "``F16En``",                     "0"
   "``F16AltEn``",                  "0"
   "``F8En``",                      "0"
   "``FVecEn``",                    "0"
   "``MMUEn``",                     "1"
   "``InstrTlbEntries``",           "16"
   "``DataTlbEntries``",            "16"
   "``RASDepth``",                  "0"
   "``BTBEntries``",                "0"
   "``BHTEntries``",                "0"
   "``NrNonIdempotentRules``",      "2"
   "``NonIdempotentAddrBase``",     "{64’b0, 64’b0}"
   "``NonIdempotentLength``",       "{64’b0, 64’b0}"
   "``NrExecuteRegionRules``",      "3"
   "``ExecuteRegionAddrBase``",     "{64’h8000_0000,64’h1_0000,64’h0}"
   "``ExecuteRegionLength``",       "{64’h4000_0000,64’h10000,64’h1000}"
   "``NrCachedRegionRules``",       "1"
   "``CachedRegionAddrBase``",      "{64’h8000_0000}"
   "``CachedRegionLength``",        "{64’h4000_0000}"
   "``NrPMPEntries``",              "4"
   "``DmBaseAddress``",             "0"
   "``CvxifEn``",                   "1"
   "``RVFI_TRACE (define)``",       "1"
   "``FIRESIM_TRACE (define)``",    "0"
   "``PITON_ARIANE (define)``",     "0"
   "``WT_CACHE (define)``",         "1"
   "``DepthStoreBuffer``",          "4"
   "``IcacheSetAssoc``",            "4"
   "``DcacheSetAssoc``",            "4"
   "``NrLoadPipeRegs``",            "1"
   "``NrStorePipeRegs``",           "0"
   "``AxiCompliant``",              "1"
   "``SwapEndianess``",             "0"
   "``FetchUserEn``",               "0"
   "``FetchUserWidth``",            "32"
   "``DataUserEn``",                "0"
   "``DataUserWidth``",             "32"
   "``RenameEn``",                  "0"
   "``NrCommitPorts``",             "1"
   "``NrScoreboardEntries``",       "4"
   "``FpgaEn``",                    "0"
