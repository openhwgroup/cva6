import re
import os
import logging
import riscv_config.utils as utils
import textwrap
import random
import pprint as pp

logger = logging.getLogger(__name__)

class warl_class():
    """This is a class for handling various operations and checks for the WARL
    type of registers and/or subfields as defined by the riscv-config spec<TODO:
    link here>. While riscv-config remains to be the major user of this package,
    this class can be used as an importable python package as well in several
    other scenarios to perform checks on a particular WARL string.

    The basic WARL node should be dict adhering to the following syntax:

    .. code-block:: yaml

        warl:
           dependency_fields: [list]
           legal: [list of warl-string]
           wr_illegal: [list of warl-string]

    :param node: This input is the dict adhering to the above syntax.
    :type node: dict
    :param csrname: this is string indicating the name of the csr or
        csr::subfield which is defined as a WARL type. This primarily used to
        generate a series of legible error and debug messages. If the input warl
        node is for a subfield, then use ``::`` as the delimiter between the csr
        name and the subfield name.
    :type csrname: str
    :param f_msb: the max msb location of the csr or subfield.
    :type f_msb: int
    :param f_lsb: the min lsb location of the csr or subfield.
    :type f_lsb: int
    :param spec: This is the entire isa-spec of a single hart. This dict is
        primarily used by this class to perform specific checks on reset-vals
        and on dependency_vals string validity.
    :type spec: dict

    """

    def __init__(self, node, csrname, f_msb, f_lsb, spec=None):
        """Constructor Method
        """

        self.node = node
        self.f_msb = f_msb
        self.f_lsb = f_lsb
        self.bitlen = f_msb - f_lsb + 1
        self.maxval = (2**(self.bitlen))-1
        self.spec = spec
        self.regex_legal = re.compile('\[(.*?)\]\s*(bitmask|in|not in)\s*\[(.*?)\]')
        self.regex_dep_legal = re.compile('(?P<csrname>.*?)\s*\[(?P<indices>.*?)\]\s*(?P<op>in|not in.*?)\s*\[(?P<values>.*?)\]\s*')
        self.dependencies = node['dependency_fields']
        self.uarch_depends = {'uarch_signals': []}
        try:
            if spec is not None:
                self.uarch_signals = spec['uarch_signals']
            else:
                self.uarch_signals = {}
        except KeyError:
            self.uarch_signals = {}
        self.csrname = csrname
        if spec is not None:
            self.isa = 'rv32' if '32' in spec['ISA'] else 'rv64'
        self.create_uarch_depends(self.uarch_signals)

    def check_subval_legal(self, legalstr, value):
        """This function checks if a given value satifies the conditions present
        in a given legal string.

        :param legalstr: This is a string following the warl-legal syntax.
        :type legalstr: str
        :param value: The value whose legality to be checked against the
            warl-legal string
        :type value: int
        :return: A list of error strings encountered while performing the
            checks on a legal string
        :rtype: list(str)

        The legal string is first broken down into smaller substrings, each of
        which assigns certain bits a specific value. Each substring should match
        the following regular-expression: ``\[(.*?)\]\s*(bitmask|in|not in)\s*\[(.*?)\]``

        For each substring, we then extract the indicies of the csr/subfield
        that are being assigned, the operation used (one of `bitmask`, `in` or
        `not in`) and values being assigned. Using the indices we extract the
        relevant sub-value of the input value argument which applies to these
        indices (we refer to this as subval).

        In case of a ``bitmask`` operation all values of the input are considered
        legal - since the mask and fixedval will ensure only legal values are
        set.

        In case of an ``in`` operation, the values list (extracted from the
        substring) is split into individual elements. Each element can either be
        a range or a single integer. In case of a range we check if the input
        subval falls within this range or not. In case of a single integer we
        perform a direct match. We parse the entire values list and stop as soon
        as atleast on match is detected.

        In case of a ``not in`` operation, the procedure is the same as above,
        except we parse through the entire values list to ensure the subval
        doesn't match any of those values, only then the subval is treated as a
        legal value.

        """
        assigns = self.regex_legal.findall(legalstr)
        err = []
        for a in assigns:
            (indices, op, vals) = a
            msb = int(indices.split(':')[0], 0)
            if ':' in indices:
                lsb = int(indices.split(':')[1], 0)
            else:
                # if its a single value, then lsb and msb are the same
                lsb = msb
            bitlen = msb - lsb + 1

            if value > self.maxval:
                err.append(f' for csr "{self.csrname}" the value {hex(value)} is out of bounds')
                continue

            # extract the value of the bits for which this particular substring
            # is applicable.
            subval = (value >> lsb) & ((1 << bitlen)-1)
            values = vals.split(',')

            # for `in` atleast one of the vals must be a hit. If none is a hit,
            # then the value is illegal.
            if op == 'in':
                atleast_one_pass = False
                for v in values:
                    base = int(v.split(':')[0], 0)
                    if ':' in v:
                        bound = int(v.split(':')[1], 0)
                    else:
                        bound = base
                    if subval >= base and subval <= bound:
                        atleast_one_pass = True
                        break
                if not atleast_one_pass:
                    err.append(f' for csr "{self.csrname}" and warl \
sub-string "{legalstr}" the value "{hex(value)}" is not legal since it fails the condition \
"[{indices}] {op} [{vals}]"')
                    break
            # for `not in` even a single match will treat the value as illegal.
            elif op == 'not in':
                all_pass = True
                for v in values:
                    base = int(v.split(':')[0], 0)
                    if ':' in v:
                        bound = int(v.split(':')[1], 0)
                    else:
                        bound = base
                    if subval >= base and subval <= bound:
                        all_pass = False
                if not all_pass:
                    err.append(f' for csr "{self.csrname}" and warl \
sub-string "{legalstr}" the value "{value}" is not legal since it fails the condition \
"[{indices}] {op} [{vals}]"')
                    break
            # for bitmask all values are treated as legal.
            elif op == 'bitmask':
                continue
            else:
                err.append(f' found op:"{op}" in legal string :"{legalstr}" \
which is not supported')
                break

        return err

    def getlegal(self, dependency_vals=[]):
        '''
        This function is used to return a legal value for a given set of
        dependency_vals. If the dependency_vals is empty and self.dependencies
        is not empty, then the first legal string is picked and the
        assignment-string substring is dierctly evaluated to get a legal value.

        :param dependency_vals: This is dictionary of csr:value pairs which
            indicates the current value of csrs/subfields present in the
            dependency_fields of the warl node.
        :type dependency_vals: dict

        :return: A single integer value which is considered legal for the csr
            under the provided dependency_vals arg
        :rtype: int
        '''
        logger.debug(f'Deriving a legal value for csr:{self.csrname}')
        err = []
        value = 0
        index = -1
        if self.dependencies and dependency_vals:
            for legalstr in self.node['legal']:
                index = index + 1
                depstr = legalstr.split('->')[0]
                # we replace all boolean operators first to simple parse and the
                # check if the (in|not in|bitmask) operators are infact legal or
                # not.
                raw_depstr = re.sub('\(|\)|and|or','',depstr)

                # implicitly assume it passes - in case of writeval and currval.
                dep_pass = False
                for m in self.regex_dep_legal.finditer(raw_depstr):
                    (csrname, indices, op, vals) = m.groups()
                    matchstr = m.group()

                    # in case the dependency is on writeval then we
                    # assume the condition is always true.
                    if csrname in ['writeval']:
                        depstr = depstr.replace(matchstr, 'True')
                        continue
                    # in case the dependency is on the current val of the same
                    # csr (before performing the write), then we continue by
                    # replacing the currval string with the csrname::subfield
                    # syntax
                    if csrname == 'currval':
                        if '::' in self.csrname:
                            renamed_csr = self.csrname.split('::')[0]
                            subfield = self.csrname.split('::')[1]
                        else:
                            renamed_csr = self.csrname
                            subfield = ''
                    else:
                        _csrname = re.sub('{\d*}','',csrname)
                        renamed_csr = list(filter(re.compile(f'[a-zA-Z0-9]*[:]*{_csrname}\s*$').match, self.dependencies))[0]
                        if '::' in renamed_csr:
                            subfield = renamed_csr.split('::')[1]
                        else:
                            subfield = ''
                        renamed_csr = renamed_csr.split('::')[0]
                    # if the dependency_vals dict is not empty, then pick the
                    # values of the csrs/subfields from there. Here we expect
                    # the key in the dependency_vals dict to be a subfield
                    # name without the `::` delimiter.
                    if csrname not in dependency_vals:
                        err.append(f'in warl string of {self.csrname}, \
the value of dependency field {csrname} not present in dependency_vals')
                        return err, value
                    else:
                        dep_csr_val = dependency_vals[csrname]
                    step_err = self.check_subval_legal(matchstr, dep_csr_val)
                    err = err + step_err
                    step_pass = True if step_err == [] else False
                    depstr = depstr.replace(matchstr, str(step_pass))
                dep_pass = eval(depstr)
                if not dep_pass:
                    continue
                else:
                    break
        else:
            index = 0
            dep_pass = True

        if not dep_pass:
            err.append(f'Cannot find a single legal string for which dependencies are satisfied')
            return err, value

        lstr = self.node['legal'][index].split('->')[-1]
        for assigns in self.regex_legal.findall(lstr):
            (indices, operation, vals) = assigns

            msb = int(indices.split(':')[0], 0)
            if ':' in indices:
                lsb = int(indices.split(':')[1], 0)
            else:
                # if its a single value, then lsb and msb are the same
                lsb = msb
            bitlen = msb - lsb + 1
            if operation == 'in':
                v = random.choice(vals.split(','))
                base = int(v.split(':')[0], 0)
                if ':' in v:
                    bound = int(v.split(':')[1], 0)
                else:
                    bound = base
                myval = random.randrange(base, bound+1)
                value = value | (myval << lsb)
            elif operation == 'not in':
                exclude_list = []
                for v in vals.split(','):
                    base = int(v.split(':')[0], 0)
                    if ':' in v:
                        bound = int(v.split(':')[1], 0)
                    else:
                        bound = base
                    exclude_list += list(range(base, bound+1))

                full_list = range(0,2**bitlen)
                select_list = list(set(full_list) - set(exclude_list))
                if not select_list:
                    err.append(f'Cannot find a legal value since \
{assigns} uses a not-in operation across the entire range')
                    return err,value
                myval = random.choice(select_list)
                value = value | (myval << lsb)
            elif operation == 'bitmask':
                mask = int(vals.split(',')[0], 0)
                fixedval = int(vals.split(',')[1], 0)
                myval = random.randrange(0,2**bitlen)
                myval = (myval & mask) | (~mask & fixedval)
                value = (myval << lsb)
        return err, value


    def islegal(self, value, dependency_vals=None):
        """This function is used to check if an input value is a legal value for
        csr for given set of dependency values. The legality is checked against
        all warl string listed under the `legal` node of the warl dictionary.

        :param value: input integer whose legality needs to be checked for the
            csr/subfield warl node.
        :type value: int
        :param dependency_vals: This is dictionary of csr:value pairs which
            indicates the current value of csrs/subfields present in the
            dependency_fields of the warl node.
        :type dependency_vals: dict

        If the dependency_fields of the warl node is empty, then the single
        legal string in the legal list, is simply processed by the function
        :py:func:`check_subval_legal` and result of which is simply returned as
        is.

        However, if the dependency_fields is not empty, then for each legal
        string we check if both dependency_vals substring is satisfied and the
        assignment substring is also satisfied, else an error is generated.

        for the dependency_vals substring the values of the csrs in the
        dependency_fields if obtained either from the input dependency_vals
        argument or else the reset-vals of the csr in the isa spec (self.spec)
        are used. If neither is available, then an error is posted about the
        same.

        The dependency_vals substring is again split further down to process
        each condition individually. The checks for the dependency_vals
        substring include:

            - checking is the csrs in the substring are indeed present in the
              dependency_fields list of the warl node
            - if writeval or currval is detected, then that part of the
              conditions is ignored.

        The dependency_vals substring is treated as a boolean condition. Hence,
        when when each part of the substring is evaluated, we replace that part
        of the string with either True or False, and at the end perform an
        `eval` on the new replaced dependency_vals substring. If this condition
        evaluates to True, the corresponing assign string also evaluates to
        True, then the input value is considered legal.

        Things this function does not do:

            - this does not check if the warl strings are valid. It is assumed
              that they are valid. If not, pass them through the function iserr
              to check for validity.
            - in case of dependency_fields being not empty, this function
              doesn't check if the possible values of the dependency
              csrs/subfields are indeed legal for them. This causes a nesting
              problem, which is probably doesn't warrant an immediate solution ??
            -
        """
        logger.debug(f'---- WARL Value Legality Check: value:{value} csr:{self.csrname} dependency_vals:{dependency_vals}')
        err = []
        # if no dependencies then only one legal string is present. Simply use
        # check_subval_legal function to detect legality.
        if not self.dependencies:
            for legalstr in self.node['legal']:
                err = self.check_subval_legal(legalstr, value)
        # in case of dependencies there can be multiple legal strings. We split
        # the legal strings into dependency strings and assign strings. Each
        # substring needs to be validated to indicate that value is indeed legal
        # for the current set of dependency vals.
        else:
            for legalstr in self.node['legal']:
                depstr = legalstr.split('->')[0]
                # we replace all boolean operators first to simple parse and the
                # check if the (in|not in|bitmask) operators are infact legal or
                # not.
                raw_depstr = re.sub('\(|\)|and|or','',depstr)

                # implicitly assume it passes - in case of writeval and currval.
                dep_pass = True
                for m in self.regex_dep_legal.finditer(raw_depstr):
                    (csrname, indices, op, vals) = m.groups()
                    matchstr = m.group()

                    # in case the dependency is on writeval then we
                    # assume the condition is always true.
                    if csrname in ['writeval']:
                        depstr = depstr.replace(matchstr, 'True')
                        continue
                    # in case the dependency is on the current val of the same
                    # csr (before performing the write), then we continue by
                    # replacing the currval string with the csrname::subfield
                    # syntax
                    if csrname == 'currval':
                        if '::' in self.csrname:
                            renamed_csr = self.csrname.split('::')[0]
                            subfield = self.csrname.split('::')[1]
                        else:
                            renamed_csr = self.csrname
                            subfield = ''
                    else:
                        _csrname = re.sub('{\d*}','',csrname)
                        renamed_csr = list(filter(re.compile(f'[a-zA-Z0-9_]*[:]*{_csrname}\s*$').match, self.dependencies))[0]
                        if '::' in renamed_csr:
                            subfield = renamed_csr.split('::')[1]
                        else:
                            subfield = ''
                        renamed_csr = renamed_csr.split('::')[0]
                    # if the dependency_vals dict is not empty, then pick the
                    # values of the csrs/subfields from there. Here we expect
                    # the key in the dependency_vals dict to be a subfield
                    # name without the `::` delimiter.
                    if dependency_vals is not None:
                        if csrname not in dependency_vals:
                            err.append(f'in warl string of {self.csrname}, \
the value of dependency field {csrname} not present in dependency_vals')
                            return err
                        else:
                            dep_csr_val = dependency_vals[csrname]
                    # else we pick the reset-vals from the isa spec (if the isa
                    # spec was provided during contruction of the class). If the
                    # dependency field is a subfield, then the reset-val of the
                    # subfield has to be extracted from the reset-val of the csr
                    elif self.spec is not None:
                        if '{' in csrname:
                            index_val = int(re.findall('{(\d*?)}',csrname)[0],0)
                            logger.debug(f'dependent csr is indexed with val {index_val}')
                            for i in self.spec[renamed_csr][self.isa]['index_list']:
                                logger.debug(f'parsing {i["index_val"]}')
                                if index_val == i['index_val']:
                                    dep_csr_val = i['reset-val']
                                    break
                        else:
                            if 'uarch_' in renamed_csr:
                                dep_csr_val = self.uarch_signals[renamed_csr]['reset-val']
                            else:
                                dep_csr_val = self.spec[renamed_csr]['reset-val']
                        if subfield != '':
                            if 'uarch_' in renamed_csr:
                                msb = self.uarch_signals[renamed_csr]['subfields'][subfield]['msb']
                                lsb = self.uarch_signals[renamed_csr]['subfields'][subfield]['lsb']
                            else:
                                msb = self.spec[renamed_csr][self.isa][subfield]['msb']
                                lsb = self.spec[renamed_csr][self.isa][subfield]['lsb']
                            bitlen = msb - lsb + 1
                            dep_csr_val = (dep_csr_val >> lsb) & \
                                ((1 << bitlen)-1)
                    else:
                        err.append(f'No dependency_vals or spec exists to \
check the values of the csrs in the dependency_fields of csr {self.csrname}')
                        return err

                    step_err = self.check_subval_legal(matchstr, dep_csr_val)
                    err = err + step_err
                    step_pass = True if step_err == [] else False
                    depstr = depstr.replace(matchstr.strip(), str(step_pass))
                dep_pass = eval(depstr)

                assignstr = legalstr.split('->')[1]
                assign_err = self.check_subval_legal(assignstr, value)
                err = err + assign_err
                assign_legal = True if assign_err == [] else False
                # if at any point both dependency strings and the assign strings
                # pass, then throw away the errors and treat it as a pass.
                if assign_legal and dep_pass:
                    logger.debug(f' warl legal string "{legalstr}" treats the \
input value {value} as legal')
                    err = []
                    break
        return err

    def create_uarch_depends(self, uarch_signals):
        '''
        This function populates the uarch_depends dict with the csr/subfield
        '''

        csrname = self.csrname
        reg_lsb = 0
        if self.f_lsb != 0:
            reg_msb = self.f_msb - self.f_lsb
        else:
            reg_msb = self.f_msb
        reg_bitlen = reg_msb - reg_lsb + 1
        for legalstr in self.node['legal']:
            depstr = legalstr.split('->')[0]
            raw_depstr = re.sub('\(|\)|and|or|\&\&|\|\|','',depstr)
            dep_str_matches = self.regex_dep_legal.findall(raw_depstr)

            if '->' in legalstr:
                dependencies = self.node['dependency_fields']
                if dependencies != [] and self.spec is not None:
                    for d in dependencies:
                        subfield = ''
                        if '::' in d:
                            depcsrname = d.split('::')[0]
                            subfield = d.split('::')[1]
                        else:
                            depcsrname = d

                        # if the depcsrname has the 'uarch_' prefix, then drop that dependency for all checks entirely
                        if depcsrname.startswith('uarch_'):
                            subfield_str = '' if subfield == '' else f'{subfield} field from '
                            logger.warning(f'WARL for csr {csrname} depends on \
{subfield_str}uarch csr {depcsrname}. Treating this as a uarch dependency.')
                            if subfield == '':
                                subfield = depcsrname
                                depcsrname = 'uarch_signals'
                            if depcsrname not in self.uarch_depends:
                                self.uarch_depends[depcsrname] = []
                            if subfield != '' and subfield not in self.uarch_depends[depcsrname]:
                                self.uarch_depends[depcsrname].append(subfield)
                            logger.debug(f'uArch dependencies are: {self.uarch_depends}')

        for entry, signode in self.uarch_depends.items():
            if signode == []:
                continue
            else:
                # grouped uarch signals
                if entry in uarch_signals:
                    for subfield in signode:
                        if subfield in uarch_signals[entry]['subfields']:
                            logger.debug(f'found csr {csrname} to depend on uArch signal {entry} \
for the following subfields: {signode}.')
                        else:
                            logger.error(f'csr {csrname} depends on uArch signal {entry} \
for the following subfields: {signode} but the uArch signal is not defined.')
                # ungrouped uarch signals
                else:
                    for entry in signode:
                        if entry in uarch_signals:
                            logger.debug(f'found csr {csrname} to depend on uArch signal {entry}.')
                        else:
                            logger.error(f'csr {csrname} depends on uArch signal {entry} \
but the uArch signal is not defined.')

    def iserr(self):
        logger.debug(f'---- Checking for Errors in {self.csrname}')
        csrname = self.csrname
        reg_lsb = 0
        if self.f_lsb != 0:
            reg_msb = self.f_msb - self.f_lsb
        else:
            reg_msb = self.f_msb
        reg_bitlen = reg_msb - reg_lsb + 1
        err = []
        #basic checks
        #if dependencies is empty, then there should be only one legal string
        if self.dependencies == [] and len(self.node['legal']) > 1:
            err.append(f'for In absence of dependencies there should be only \
1 legal string, instead found {len(self.node["legal"])}')
        if err:
            return err

        # start checking legality of all legal strings
        for legalstr in self.node['legal']:
            depstr = legalstr.split('->')[0]
            raw_depstr = re.sub('\(|\)|and|or|\&\&|\|\|','',depstr)
            dep_str_matches = self.regex_dep_legal.findall(raw_depstr)

            # if there are no dependencies then "->" should never be used in the
            # warl legal strings
            if '->' in legalstr and self.dependencies == []:
                err.append(f' found "->" in legal string "legalstr" when \
dependency_fields is empty.')
                return err
            if self.dependencies != [] and not '->' in legalstr:
                err.append(f' missing "->" in legalstr since dependency_fields \
is non empty')
                return err

            if '->' in legalstr:
                dependencies = self.node['dependency_fields']
                if dependencies != [] and self.spec is not None:
                    for d in dependencies:
                        subfield = ''
                        if '::' in d:
                            depcsrname = d.split('::')[0]
                            subfield = d.split('::')[1]
                        else:
                            depcsrname = d

                        # if the csr is a uarch dependency and also exists in the spec, throw an error
                        if depcsrname in self.uarch_depends and depcsrname in self.spec:
                            err.append(f' csr {csrname} depends on uarch csr \
{depcsrname} which is also present in the spec. This is not allowed.')

                        # if the dependency is on writeval or currval of the
                        # same csr, or is a uArch dependency, then no more checks required.
                        if depcsrname not in ['writeval', 'currval'] and depcsrname not in self.uarch_depends and depcsrname not in self.uarch_depends['uarch_signals']:
                            # if the csr doesn't exist then its probably a typo
                            if depcsrname not in self.spec:
                                err.append(f' warl for csr {csrname} depends on csr \
{depcsrname} is not a valid csrname as per spec')
                            # if csr exists, but is not accessible, then its a
                            # pointless dependency
                            elif not self.spec[depcsrname][self.isa]['accessible']:
                                err.append(f' warl for csr {csrname} depends on csr \
{depcsrname} is not accessible or not implemented in the isa yaml')
                            # if csr exists and is accessible but subfield
                            # doesn't exist, then its another typo
                            elif subfield != '' and subfield not in self.spec[depcsrname][self.isa]:
                                err.append(f' warl for csr {csrname} depends on \
subfield {depcsrname}::{subfield} which does not exist as per spec')
                            # if subfield is valid, but is not implemented, then
                            # its another pointless dependency
                            elif subfield !='' and not self.spec[depcsrname][self.isa][subfield]['implemented']:
                                err.append(f' warl for csr {csrname} depends \
on subfield {depcsrname}::{subfield} which is not implemented')

                    # ensure that all dependency csrs/subfields found in the
                    # strings, are indeed present in the dependency_fields list
                    # of the warl node.
                    for matches in dep_str_matches:
                        (csr, ind, op, val) = matches
                        csr = re.sub('{\d*}','', csr)
                        csr_in_dependencies = list(filter(re.compile(f'[a-zA-Z0-9_]*[:]*{csr}\s*$').match, dependencies))
                        if csr_in_dependencies == []:
                            for entry, subfields in self.uarch_signals.items():
                                if csr == entry:
                                    csr_in_dependencies.append(csr)
                                elif csr in subfields['subfields']:
                                    csr_in_dependencies.append(f'{csr}::{subfield}')
                        if csr_in_dependencies == []:
                            err.append(f' dependency_vals string "{depstr}" for csr \
{csrname} is dependent on field {csr} which is not present in the \
dependency_fields list of the node')

                for matches in dep_str_matches:
                    (csr, indices, op, val) = matches
                    # only in and not-in are supported inside dependency
                    # strings. Bitmask do not make sense as a boolean operation.
                    if op not in ['in', 'not in']:
                        err.append(f' the dependency_vals string {depstr} for csr \
{csr} uses operation "{op}" which is not supported. Use only "in" and "not in" \
operations only')

                    msb = int(indices.split(':')[0], 0)
                    if ':' in indices:
                        lsb = int(indices.split(':')[1], 0)
                    else:
                        lsb = msb
                    # for range value strings, indices msb::lsb syntax to be
                    # followed where msb > lsb
                    if msb < lsb:
                        err.append(f'msb < lsb for one of the \
dependency_vals in warl string {legalstr} in csr {csrname}')
                    maxval = 2**(msb - lsb + 1 )
                    values = val.split(',')

                    # for each range value, check if the base and bound are
                    # correctly ordered and within the possible values of the
                    # csr/subfield
                    for v in values:
                        base = int(v.split(':')[0], 0)
                        if ':' in v:
                            bound = int(v.split(':')[1], 0)
                        else:
                            bound = base
                        if base >= maxval or bound >= maxval:
                            err.append(f'The range values in dependency_vals of warl\
 string "{legalstr}" for csr {csrname} are out of bounds wrt the indices used \
in that string')
                        if base > bound:
                            err.append(f' base > bound for range \
values in dependency_vals of the warl string "{legalstr}" for csr {csrname}')

            lstr = legalstr.split('->')[-1]
            bitcount = reg_bitlen

            assigns = self.regex_legal.findall(lstr)
            # if there is not match, then something is wrong in the string.
            if assigns == []:
                err.append(f' The legal string "{legalstr}" for csr \
{csrname} does not follow warl syntax')
            # split the assignment string and process each individually.
            for a in assigns:
                (indices, op, vals) = a

                # msb lsb checks just as before
                msb = int(indices.split(':')[0], 0)
                if ':' in indices:
                    lsb = int(indices.split(':')[1], 0)
                else:
                    lsb = msb
                if msb < lsb:
                    err.append(f'msb < lsb for one of the \
range values in warl string {legalstr} in csr {csrname}')
                if msb > reg_msb or lsb < reg_lsb:
                    err.append(f' The indices used in warl \
string "{legalstr}" of csr {csrname} do not comply with the msb[{reg_msb}] and lsb[{reg_lsb}] values \
of the register')

                # we need to ensure that the assignment string eventually
                # defines the legal value for all the bits (and not just a few).
                # To check this we use a counter (bitcount) which is initialized
                # to the size of the register/subfield. And each time a part of
                # the assignment string is evaluated, we decrease the bitcount
                # by the size of the assigment. At the end, if the bitcount is
                # not zero then there is something wrong in the entire
                # assignment string.
                bitcount = bitcount - (msb-lsb+1)
                bitlength = msb - lsb + 1
                reg_maxval = 2**bitlength
                maxval = 2**bitlength
                if op not in ['in', 'not in', 'bitmask']:
                    err.append(f' the warl string {legalstr} for csr \
{csr} uses operation "{op}" which is not supported. Use only "in", "bitmask" and "not in" \
operations only')
                if 'bitmask' in op:
                    if len(vals.split(',')) != 2:
                        err.append(f'bitmask syntax is wrong in legal string \
{legalstr}')
                        break
                    mask = int(vals.split(',')[0], 0)
                    fixedval = int(vals.split(',')[1], 0)
                    if mask > reg_maxval or fixedval > reg_maxval:
                        err.append(f' The mask and/or fixedval used in \
bitmask string "{legalstr}" of csr {csrname} have values exceeding the \
maxvalue the csr can take.')
                else:
                    values = vals.split(',')
                    for v in values:
                        base = int(v.split(':')[0], 0)
                        if ':' in v:
                            bound = int(v.split(':')[1], 0)
                        else:
                            bound = base
                        if base >= maxval or bound >= maxval:
                            err.append(f'The range values in warl \
string "{legalstr} for csr {csrname} are out of bounds wrt the indices used \
in that string')
                        if base > bound:
                            err.append(f' base > bound for range \
values in warl string "{legalstr}" for csr {csrname}')

            if bitcount < 0:
                err.append(f' warl string "{legalstr}" defines values for bits \
outside the size of the register "{reg_bitlen}"')
            elif bitcount != 0:
                err.append(f' warl string "{legalstr}" for csr \
"{csrname}" either does not define values for all bits or has overlapping ranges \
defining the same bits multiple times')

        return err

