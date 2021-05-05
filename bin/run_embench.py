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
# run_embench : python script to fetch, set up, build and run EMBench 
#               benchmarking suite on the present cores
#
# Author: Marton Teilgård
#  email: mateilga@silabs.com
#
# Written with Python 3.6.5 on RHEL 7.7.  Your python mileage may vary.
#
# Restriction:
#
#
################################################################################

import argparse
import logging
import os
import sys
import subprocess
import jinja2
import glob
import re



def main():

  check_python_version(3,6)

  parser = build_parser()
  args = parser.parse_args()
  paths = build_paths(args.core)

  if args.debug == 'YES':
    log_level = logging.DEBUG
  else:
    log_level = logging.WARNING

  logging.basicConfig(level=log_level, format='%(levelname)s: %(message)s')


  if args.core == 'notset':
    print('Must specify a core to benchmark')
    sys.exit(1)

  if args.ccomp == 'notset':
    print('Must specify a c compiler to benchmark')
    sys.exit(1)

  if args.type != 'speed' and args.type != 'size':
    print(f"Invalid type selected: {args.type}, must be 'speed' or 'size'")
    sys.exit(1)

  if args.build_only == 'YES':
    build_only = True
  elif args.build_only == 'NO':
    build_only = False
  else:
    print(f"Invalid 'build_only' option: {args.build_only}, must be 'YES' or 'NO'")
    sys.exit(1)

  print("Starting EMBench for core-v-verif")
  print(f"Benchmarking core: {args.core}")
  print(f"Type of benchmark to run: {args.type}\n\n")


  # checking if there are existing configuration files
  if os.path.exists(paths['emcfg']):
    logging.info("EMBench repository checked out previously. \n Cleaning results and skipping cfg copy")
    prebuilt = True
    # deleting existing build results
    try:
      subprocess.run(
        ['find', '.', '!', '-path', '.', '!', '-path', './README.md', '-delete'],
        cwd=paths['testsem']
      )
    except:
      logging.fatal('Failed to delete old build results')
  else:
    prebuilt = False

  
  print("Building Benchmark files")


  if not prebuilt:
    # copy core-native config
    logging.info(f"Copying EMBench config from {paths['libcfg']} to {paths['emcfg']}")
    try:
      subprocess.run(
        ['cp', '-R', paths['libcfg'], paths['emcfg']]
      )
    except:
      logging.fatal('EMBench config copy failed')

    # copy source files from bsp
    # Only done when testing speed, size benchmark is built without support
    # to matchEMBench baseline
    if args.type == 'speed':
      logging.info(f"Copying files from {paths['bsp']} to {paths['embrd']}")
      for file in os.listdir(paths['bsp']):
        if file.endswith('.S') or file.endswith('.c'):
          logging.info(f"Copying {file}")
          try:
            subprocess.run(['cp', paths['bsp']+'/'+file, paths['embrd']])
          except:
            logging.fatal(f"EMBench bsp copy of file {file} failed")

    # copy python module
    logging.info(f"Copying {paths['libpy']}/run_corev32.py to {paths['empy']}/run_corev32.py")
    try:
      subprocess.run(
        ['cp', f"{paths['libpy']}/run_corev32.py", f"{paths['empy']}/run_corev32.py"]
      )
    except:
      logging.fatal('EMBench python module copy failed')



  # build EMBench library
  logging.info(f"Calling build script")
  try: 
    res = subprocess.run(
      ['build_all.py', '--arch=corev32', '--board=corev32', f"--chip={args.type}", f"--cc={args.ccomp}", f"--ldflags=-T{paths['bsp']}/link.ld", '--clean'],
      stdout=subprocess.PIPE,
      stderr=subprocess.PIPE,
      cwd=paths['embench']
    )
  except:
    logging.fatal('EMBench build failed')

  if build_passed(res.stdout.decode('utf-8')):
    print(f"EMBench for {args.type} built successfully")
  else:
    logging.fatal('EMBench build failed')
    sys.exit(1)

  # build test directory, copy and rename the executable test files, and generate yaml files
  # This is not done if the built files are for the size benchmark, as these are not able to run
  if args.type == 'speed':
    for folder in os.listdir(paths['emres']):
      # create test directory
      folder_ext = f"emb_{folder}"
      
      logging.info(f"Creating folder {paths['testsem']}/{folder_ext}")
      try:
        subprocess.run(['mkdir', f"{paths['testsem']}/{folder_ext}"])
      except:
        logging.fatal(f"Failed to generate folder {paths['testsem']}/{folder_ext}")
        sys.exit(1)

      # copy test file from 
      for file in os.listdir(f"{paths['emres']}/{folder}"):
        if not file.endswith('.o'):
          logging.info(f"Copying file {file}")
          try:
            subprocess.run(['cp', f"{paths['emres']}/{folder}/{file}", f"{paths['testsem']}/{folder_ext}/emb_{file}.elf"])
          except:
            logging.fatal(f"Copying file {file} to {paths['emres']}/{folder_ext}/ failed")
            sys.exit(1)
          
          break
      
      # generate test.yaml
      logging.info(f"Rendering template: test.yaml.j2 for test: {folder_ext}")
      generate_test_yaml(f"{paths['testsem']}/{folder_ext}", folder_ext)


  if build_only: 
    print("Build only selected, exiting")
    sys.exit()

  # run benchmark script
  print(f"Starting benchmarking of {args.type}")

  if args.type == 'speed':
    arglist = ['benchmark_speed.py', '--target-module=run_corev32', '--timeout=1200', f"--cpu-mhz={args.cpu_mhz}", f"--make-path={paths['make']}", f"--simulator={args.simulator}"]
  else:
    arglist = ['benchmark_size.py']

    
  try:
    res = subprocess.run(
      arglist,
      stdout=subprocess.PIPE,
      stderr=subprocess.PIPE,
      universal_newlines=True,
      cwd=paths['embench'],
      )

  except:
      logging.fatal(f"EMBench script benchmark_{args.type}.py failed")
      sys.exit(1)


  #Check if benchmark run succeeded
  if not run_passed(res.stdout, args.type):
    logging.fatal(f"EMBench benchmark run failed")
    log_file = get_log_file(args.core, paths, args.type)
    if log_file:
        logging.info('For more debug check EMBench log: {}'.format(log_file))
    sys.exit(1)

  if check_result(res.stdout, args.target, args.type) and args.target != 0:
    print(f"Benchmark run met target")
  elif args.target != 0:
    print(f"Benchmark run failed to meet the target: {args.target}")




###############################################################################
# End of Main  

def build_parser():
  """Build a parser for all the arguments"""
  parser = argparse.ArgumentParser(description='Clone and run EMBench', formatter_class=argparse.RawTextHelpFormatter)

  parser.add_argument(
    '-c',
    '--core',
    default='notset',
    help='Core to benchmark'
  )

  parser.add_argument(
    '-cc',
    '--ccomp',
    default='notset',
    help='C compiler for benchmark'
  )

  parser.add_argument(
    '-t',
    '--type',
    default='speed',
    help=(
      'What benchmark to run. Valid options: speed, size\n'+
      'Default option: speed \n'+
      'NOTE: type affects build configuration!\n'+
      'makefile alias: EMB_TYPE'
    )
  )

  parser.add_argument(
    '-b',
    '--build-only',
    default='NO',
    help=(
      'Set this option to "YES" to only build the benchmarks.\n'+
      'Type option is still honored\n'+
      'makefile alias: EMB_BUILD_ONLY'
    )
  )

  parser.add_argument(
    '-tgt',
    '--target',
    type=float,
    default=0,
    help=(
      'Set a target for your EMBench score\n'+
      'Benchmark run will fail if target is not met\n'+
      'If no target is set, no checking is done\n'+
      'makefile alias: EMB_TARGET'
    )
  )

  parser.add_argument(
    '-f',
    '--cpu-mhz',
    default=1,
    help=(
      'Set the core frequency in MHz.\n'+
      'Default is 1 MHz\n'+
      'makefile alias: EMB_CPU_MHZ'
    )
  )

  parser.add_argument(
    '-sim',
    '--simulator',
    default='xrun',
    help=(
      'Simulator to run the benchmarks\n'+
      'makefile alias: SIMULATOR'
    )
  )

  parser.add_argument(
    '-d',
    '--debug',
    default='NO',
    help=(
      'Set this option to "YES" to increase verbosity of the script\n'+
      'makefile alias: EMB_DEBUG'
    )
  )
  
  return parser

def build_paths(core):
  """map out necessary paths"""
  paths = dict()
  paths['cver'] = os.path.abspath(os.path.join(os.path.dirname(__file__), os.pardir))
  paths['core'] = paths['cver'] + '/' + core
  paths['libcfg'] = paths['core'] + '/tests/embench/config/corev32'
  paths['libpy'] = paths['core'] + '/tests/embench/pylib'
  paths['vlib'] = paths['core'] + '/vendor_lib'
  paths['emb_logs'] = paths['core'] + '/vendor_lib/embench/logs'
  paths['make'] = paths['core'] + '/sim/uvmt'
  paths['embench'] = paths['vlib'] + '/embench'
  paths['emcfg'] = paths['embench'] + '/config/corev32'
  paths['empy'] = paths['embench'] + '/pylib'
  paths['embrd'] = paths['emcfg'] + '/boards/corev32'
  paths['emres'] = paths['embench'] + '/bd/src'
  paths['bsp'] = paths['core'] + '/bsp'
  paths['testsem'] = paths['core'] + '/tests/programs/embench'

  return paths

def generate_test_yaml(folder, test_name):
  env = jinja2.Environment(loader=jinja2.FileSystemLoader(os.path.join(os.path.dirname(__file__),                                                         
                                                        'templates')), trim_blocks=True)
  template = env.get_template('embench_test.yaml.j2')
  
  out = open(f"{folder}/test.yaml", 'w')
  out.write(template.render(name=test_name))
  out.close()
    
def build_passed(stdout_str):
  if re.search('All benchmarks built successfully', stdout_str, re.S):
    return True
  else:
    return False

def run_passed(stdout_str, type):
  if type == 'speed':
    if re.search('All benchmarks run successfully', stdout_str, re.S):
      return True
    else:
      return False
  else: #size
    if re.search('All benchmarks sized successfully', stdout_str, re.S):
      return True
    else:
      return False

def check_result(stdout_str, tgt, type):
  #print results to screen
  print(stdout_str)
  
  #find result in numeric value and compare to target
  rcstr = re.search('Geometric mean *(\d+)[.](\d+)', stdout_str, re.S)
  result = int(rcstr.group(1)) + (int(rcstr.group(2)) * 0.01)

  if type == 'speed':
    if (tgt == 0) or (result >= tgt):
      return True
    else:
      return False
  else:
    if (tgt == 0) or (result <= tgt):
      return True
    else:
      return False


# Make sure we have new enough python
def check_python_version(major, minor):
    """Check the python version is at least {major}.{minor}."""
    if ((sys.version_info[0] < major)
        or ((sys.version_info[0] == major) and (sys.version_info[1] < minor))):
        log.error('ERROR: Requires Python {mjr}.{mnr} or later'.format(mjr=major, mnr=minor))
        sys.exit(1)

def get_log_file(core, paths, log_type):
    '''Find the log file from EMBench by looking for the latest touched file'''
    last_mtime = 0
    file = None    
    for f in glob.glob(os.path.join(paths['emb_logs'], '{}-*.log'.format(log_type))):
        if last_mtime < os.stat(f).st_mtime:
            last_mtime = os.stat(f).st_mtime
            file = f

    print('Latest log = {}'.format(file))
    return file

#run main
if __name__ == '__main__':
    sys.exit(main())
