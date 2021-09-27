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

import os
import re
import sys
import logging
from collections import OrderedDict

logger = logging.getLogger(__name__)

DEFAULT_ISS = 'YES'
DEFAULT_COV = 'NO'
DEFAULT_CFG = 'default'
DEFAULT_SIMULATION_PASSED = 'SIMULATION PASSED'
DEFAULT_SIMULATION_FAILED = 'SIMULATION FAILED'
DEFAULT_SKIP_SIM = []

def get_proj_root():
    '''Fetch absolute path of core-v-verif directory'''
    return os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

class Build:
    '''A regression build object'''
    def __init__(self, **kwargs):

        # Create defaults
        self.iss = DEFAULT_ISS
        self.cfg = DEFAULT_CFG

        for k, v in kwargs.items():
            setattr(self, k, v)

        # Absolutize a directory if dir tag exists
        self.abs_dir = os.path.abspath(os.path.join(get_proj_root(), self.dir))

    def set_cov(self):
        '''Set the coverage flag based on app setting.
        If cov already defined (from testlist), then ignore'''
        try:
            getattr(self, 'cov')
        except AttributeError:
            self.cov = True

    def sub_make(self, make_sub):
        '''In the command substitute the make with the supplied substitution'''
        self.cmd = re.sub('make', make_sub, self.cmd)

    def __str__(self):
        return '{} {} {}'.format(self.name, self.cmd, self.dir)

class Test:
    '''A regression test object'''
    def __init__(self, **kwargs):
        '''Create a test object'''

        # Set defaults
        self.skip_sim = DEFAULT_SKIP_SIM
        self.simulation_passed = DEFAULT_SIMULATION_PASSED
        self.simulation_failed = DEFAULT_SIMULATION_FAILED
        self.iss = DEFAULT_ISS
        self.num = 1
        self.builds = []

        for k, v in kwargs.items():
            setattr(self, k, v)

        # Absolutize a directory if exists
        self.abs_dir = os.path.abspath(os.path.join(get_proj_root(), self.dir))

        # Log equals the test name if does not exist
        if not hasattr(self, 'log'):
            self.log = self.name

    def set_cov(self):
        '''Set the coverage flag based on app setting.
        If cov already defined (from testlist), then ignore'''
        try:
            getattr(self, 'cov')
        except AttributeError:
            self.cov = True

    def sub_make(self, make_sub):
        '''In the command substitute the make with the supplied substitution'''
        self.cmd = re.sub('make', make_sub, self.cmd)
        try:
            self.precmd = re.sub('make', make_sub, self.precmd)
        except AttributeError:
            # precmd is optional
            pass

class Regression:
    '''A full regression object'''
    def __init__(self, **kwargs):
        '''Constructor'''
        self.builds = OrderedDict()
        self.tests = OrderedDict()

        for k, v in kwargs.items():
            setattr(self, k, v)


    def add_build(self, build):
        '''Add a new build object to this regression'''
        if build.name in self.builds.keys():
            logger.fatal('Build: {} was defined multiple times'.format(build['name']))
            os.sys.exit(2)

        self.builds[build.name] = build

    def add_test(self, test):
        '''Add a new test object to this regression'''
        if test.name in self.tests.keys():
            logger.fatal('Test: {} was defined multiple times'.format(test['name']))
            os.sys.exit(2)

        # Validate that builds exist
        try:
            for b in test.builds:
                if not b in self.builds.keys():
                    logger.fatal('Test: {} references non-existent build: {}'.format(test.name, b))
                    os.sys.exit(2)
        except TypeError:
            logger.fatal('Test: {} did not specify a list of builds'.format(test.name))
            os.sys.exit(2)

        self.tests[test.name]  = test

    def get_builds(self):
        '''Return all builds found in all tests'''

        builds = {self.builds[build] for t in self.tests.values() for build in t.builds}
        return list(builds)

    def get_builds_with_no_tests(self):
        '''Return all builds found in all tests'''

        builds_with_no_tests = []

        for b in self.builds.values():
            found = False
            for t in self.tests.values():
                if b.name in t.builds:
                    found = True
            if not found:
                builds_with_no_tests.append(b)

        return builds_with_no_tests

    def get_tests_of_build(self, build):
        '''Return all test objects that contain the given build'''

        tests = [t for t in self.tests.values() if build in t.builds]
        return tests
