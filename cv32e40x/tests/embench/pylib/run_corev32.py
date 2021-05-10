#!/usr/bin/env python3

################################################################################
#
# Copyright 2020 OpenHW Group
# 
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     https://solderpad.org/licenses/
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
# 
################################################################################
#
# run_corev32 : python module provided to EMBench to allow the run script to 
#               run simulations in core-v-verif
#
# Author: Marton Teilgård
#  email: mateilga@silabs.com
#
#
# Restriction:
#
#
# TODO:
################################################################################

"""
Embench module to run benchmark programs.

This version is part of core-v-verif integration to EMBench.
"""

__all__ = [
    'get_target_args',
    'build_benchmark_cmd',
    'decode_results',
]

import argparse
import re

from embench_core import log


def get_target_args(remnant):
    """Parse left over arguments"""
    parser = argparse.ArgumentParser(description='Get target specific args')

    parser.add_argument(
        '--cpu-mhz',
        type=int,
        default=1,
        help='Processor clock speed in MHz'
    )

    parser.add_argument(
        '--make-path',
        type=str,
        required=True,
        help='The path to run make test from'
    )

    parser.add_argument(
        '--simulator',
        type=str,
        required=True,
        help='Simulator to run the benchmarks'
    )

    return parser.parse_args(remnant)


def build_benchmark_cmd(bench, args):
    """Construct the command to run the benchmark.  "args" is a
       namespace with target specific arguments"""

    #CPU period
    global cpu_per 
    cpu_per = float(1/(args.cpu_mhz*1_000_000))
    
    #Utilize "make test" environment in core-v-verif
    return ['make', '-C', args.make_path, 'test', f"TEST=emb_{bench}", f"SIMULATOR={args.simulator}", 'USE_ISS=NO']


def decode_results(stdout_str, stderr_str):
    """Extract the results from the output string of the run. Return the
       elapsed time in milliseconds or zero if the run failed."""
  

    global cpu_per

    #check that simulation returned successfully
    if not re.search('SIMULATION PASSED', stdout_str, re.S):
        log.debug('Warning: Simulation reporting error')
        return 0.0

    # Match "RES: <cycles>"
    rcstr = re.search('RES: (\d+)', stdout_str, re.S)
    if not rcstr:
        log.debug('Warning: Failed to find result')
        return 0.0

    time = float(int(rcstr.group(1))*cpu_per)
    time_ms = time * 1000
    

    return time_ms

    # We must have failed to find a time
    log.debug('Warning: Failed to find timing')
    return 0.0
