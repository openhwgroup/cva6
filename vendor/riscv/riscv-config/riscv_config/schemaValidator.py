from cerberus import Validator
import riscv_config.constants as constants
from riscv_config.isa_validator import *
import re
from riscv_config.warl import warl_class


class schemaValidator(Validator):
    ''' Custom validator for schema having the custom rules necessary for implementation and checks.'''

    def __init__(self, *args, **kwargs):
        global rv32
        global rv64
        global extensions
        global xlen
        global supported_xlen
        supported_xlen = kwargs.get('xlen')
        xlen = 0 if len(supported_xlen)==0 else max(supported_xlen)
        global isa_string
        isa_string = kwargs.get('isa_string')
        global extension_list
        global ext_err
        global ext_err_list
        if isa_string :
          (extension_list, ext_err, ext_err_list) = get_extension_list(isa_string)
        if 32 in supported_xlen:
            rv32 = True
        else:
            rv32 = False
        if 64 in supported_xlen:
            rv64 = True
        else:
            rv64 = False
        super(schemaValidator, self).__init__(*args, **kwargs)

    def _check_with_smrnmi_check(self, field, value):
      global extension_list
      if value and 'Smrnmi' not in extension_list:
        self._error(field,
                  "Register cannot be implemented without Smrnmi extension in ISA."
              )

    def _check_with_zicfiss_check(self, field, value):
      global extension_list
      if value and 'Zicfiss' not in extension_list:
        self._error(field,
                  "Register cannot be implemented without Zicfiss extension in ISA."
              )

    def _check_with_satp_modes64(self, field, value):
        pass

    def _check_with_isa_xlen(self, field, value):
        global supported_xlen
        global isa_string
        if str(max(supported_xlen)) not in isa_string:
            self._error(field, 'XLEN in ISA and supported_xlen fields do not match')

    def _check_with_phy_addr(self, field, value):
        if rv32 and value > 34:
            self._error(field, "Physical address size should not exceed 34 for RV32")
        if rv64 and value > 56:
            self._error(field, "Physical address size should not exceed 56 for RV64")

    def _check_with_cache_block_size(self, field, value):
        if value & (value - 1) != 0:
            self._error(field, "Cache block size should be power of 2")

    def _check_with_cannot_be_false_rv64(self, field, value):
        ''' Functions ensures that the field cannot be False in rv64 mode'''
        if rv64 and not value:
            self._error(field, "This field cannot be False")
    def _check_with_cannot_be_false_rv64f(self, field, value):
        ''' Functions ensures that the field cannot be False in rv64 mode when F is present'''
        global extension_list
        if rv64 and 'F' in extension_list and not value:
            self._error(field, "This field cannot be False")
    def _check_with_cannot_be_false_rv32f(self, field, value):
        ''' Functions ensures that the field cannot be False in rv32 mode when F is present'''
        if rv32 and 'F' in extension_list and not value:
            self._error(field, "This field cannot be False")

    def _check_with_cannot_be_false_rv32(self, field, value):
        ''' Functions ensures that the field cannot be False in rv32 mode'''
        if rv32 and not value:
            self._error(field, "This field cannot be False")

    def _check_with_capture_isa_specifics(self, field, value):
        '''
        Function to extract and store ISA specific information(such as xlen,user
        spec version and extensions present)
        and check whether the dependencies in ISA extensions are satisfied.
        '''
        global xlen
        global extensions
        global extension_list
        global ext_err_list
        global ext_err
        extension_enc = list("00000000000000000000000000")
        if "32" in value:
            xlen = 32
            ext = value[4:]
        elif "64" in value:
            xlen = 64
            ext = value[4:]
        elif "128" in value:
            xlen = 128
            ext = value[5:]
        else:
            self._error(field, "Invalid width in ISA.")

        if not constants.isa_regex.match(value):
            self._error(field, 'Input ISA string does not match regex')
        if ext_err:
            for e in ext_err_list:
                self._error(field, e)

        #ISA encoding for future use.
        for x in "ABCDEFHIJKLMNPQSTUVX":
            if (x in extension_list):
                extension_enc[25 - int(ord(x) - ord('A'))] = "1"
        extensions = int("".join(extension_enc), 2)
        extensions = int("".join(extension_enc), 2)

    def _check_with_rv32_check(self, field, value):
        global xlen
        if value:
            if not rv32:
                self._error(
                    field,
                    "Register cannot be implemented in rv32 mode due to unsupported xlen."
                )

    def _check_with_rv64_check(self, field, value):
        global xlen
        if value:
            if not rv64:
                self._error(
                    field,
                    "Register cannot be implemented in rv64 mode due to unsupported xlen."
                )

    def _check_with_max_length(self, field, value):
        '''Function to check whether the given value is less than the maximum value that can be stored(2^xlen-1).'''
        global supported_xlen
        global extensions
        maxv = max(supported_xlen)
        if value > (2**maxv) - 1:
            self._error(field, "Value exceeds max supported length")

    def _check_with_max_length32(self, field, value):
        '''Function to check whether the given value is less than the maximum value that can be stored(2^xlen-1).'''
        maxv = 32
        if value > (2**maxv) - 1:
            self._error(field, "Value exceeds max supported length")

    def _check_with_xtveccheck(self, field, value):
        '''Function to check whether the inputs in range type in mtvec are valid.'''
        global xlen
        maxv = 2**(xlen - 2)
        for list in value:
            if (len(list) > 2):
                self._error(field,
                            "Only two values are allowed in each sub list.")
            for val in list:
                if not (val < maxv):
                    self._error(field, "Invalid values.")

    def _check_with_s_exists(self, field, value):
        '''Function to check that the value can be true only when 'S' mode
        exists in the ISA string'''
        global extension_list

        if value and 'S' not in extension_list:
            self._error(field, "cannot be set to True without 'S' mode support")

    def _check_with_mtval_update(self, field, value):
        '''Function to check if the mtval_update bitmap adhered to the required
        restrictions.
        '''
        global extension_list
        if (((value & 0xFFFF000F4000) != 0) or (value > 0xFFFFFFFFFFFFFFFF)):
            self._error(field, 'Bits corresponding to reserved cause values should not be set')
        if (value & 0xB000) != 0 and 'S' not in extension_list:
            self._error(field, 'Bits corresponding to page-faults can only be set when S mode is supported')
        if (value & 0xF00000) != 0 and 'H' not in extension_list:
            self._error(field, 'Bits corresponding to guest-page faults can only be set when H mode is supported')

    def _check_with_s_check(self, field, value):
        s = 18
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True

        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - s:66 - s] != '1'):
                self._error(field, "should not be implemented since S is not present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - s:34 - s] != '1'):
                self._error(field, "should not be implemented S is not present")

    def _check_with_fs_check(self, field, value):
        f = 5
        s = 18
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True

        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - s:66 - s] != '1') and (mxl[65 - f:66 - f] != '1'):
                self._error(field, "neither S nor F is present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - s:34 - s] != '1') and (mxl[33 - f:34 - f] != '1'):
                self._error(field, "neither S nor F is present")


    def _check_with_f_check(self, field, value):
        f = 5
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True
        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - f:66 - f] != '1'):
                self._error(field, "should not be implemented since F is not present")
        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - f:34 - f] != '1'):
                self._error(field, "should not be implemented since F is not present")


    def _check_with_u_check(self, field, value):
        u = 20
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True
        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - u:66 - u] != '1'):
                self._error(field, "should not be implemented since U is not present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - u:34 - u] != '1'):
                self._error(field, "should not be implemented since U is not present")

    def _check_with_s_debug_check(self, field, value):
        ''' Function ensures that the ro_constant is hardwired to zero when S is present in the ISA string
            Used mainly for debug schema'''
        global extension_list

        if 'S' not in extension_list :
          if 'ro_constant' not in value:
              self._error(field, "S is not present to dcsr.v should be ro_constant = 0")
          elif value['ro_constant'] != 0:
                self._error(field, "S is not present but ro constant is not hardwired to zero")

    def _check_with_u_debug_check(self, field, value):
        ''' Function ensures that the ro_constant is hardwired to zero when U is present in the ISA string
            Used mainly for debug schema'''
        global extension_list

        if 'U' not in extension_list :
          if value['ro_constant'] != 0:
                self._error(field, "U is not present but ro constant is not hardwired to zero")

    def _check_with_su_check(self, field, value):
        s = 18
        u = 20
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True

        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - s:66 - s] != '1') and (mxl[65 - u:66 - u] != '1'):
                self._error(field, "neither S nor U is present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - s:34 - s] != '1') and (mxl[33 - u:34 - u] != '1'):
                self._error(field, "neither S nor U is present")

    def _check_with_reset_ext(self, field, value):

        if rv64:
            mxl = format(extensions, '#066b')
            reset = format(value, '#066b')
            if (mxl[40:66] != reset[40:66] ):
                self._error(field, "reset value does not match with extensions enabled")

        elif rv32 :
            mxl = format(extensions, '#034b')
            reset = format(value, '#034b')
            if (mxl[8:34] != reset[8:34] ):
                self._error(field, "reset value does not match with extensions enabled")

    def _check_with_sn_check(self, field, value):
        s = 18
        n = 13
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True

        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - s:66 - s] != '1') and (mxl[65 - n:66 - n] != '1'):
                self._error(field, "neither S nor N is present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - s:34 - s] != '1') and (mxl[33 - n:34 - n] != '1'):
                self._error(field, "neither S nor N is present")

    def _check_with_n_check(self, field, value):
        n = 13
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True
        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - n:66 - n] != '1'):
                self._error(field, "should not be implemented since N is not present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - n:34 - n] != '1'):
                self._error(field, "should not be implemented since N is not present")

    def _check_with_h_check(self, field, value):
        h = 7
        check = False
        if 'implemented' in value:
            if value['implemented']:
                check = True
        if 'accessible' in value:
            if value['accessible']:
                check = True
        if rv64 and check:
            mxl = format(extensions, '#066b')
            if (mxl[65 - h:66 - h] != '1'):
                self._error(field, "h is not present")

        elif rv32 and check:
            mxl = format(extensions, '#034b')
            if (mxl[33 - h:34 - h] != '1'):
                self._error(field, "h is not present")

    def _check_with_mdeleg_checks(self, field, value):
        global extension_list
        if rv32:
            if (value['rv32']['accessible'] == True and
                (not 'S' in extension_list and
                 not 'N' in extension_list)):
                value['rv32']['accessible'] = False
                self._error(field, "S and N are not present")

        if rv64:
            if (value['rv64']['accessible'] == True and
                (not 'S' in extension_list and
                 not 'N' in extension_list)):
                value['rv64']['accessible'] = False
                self._error(field, "S and N are not present")

    def _check_with_ndeleg_checks(self, field, value):
        global extension_list
        if rv32:
            if (value['rv32']['accessible'] == True and
                    not 'N' in extension_list):
                value['rv32']['accessible'] = False
                self._error(field, "should not be implemented since N is not present")

        if rv64:
            if (value['rv64']['accessible'] == True and
                    not 'N' in extension_list):
                value['rv64']['accessible'] = False
                self._error(field, "should not be implemented since N is not present")

    def _check_with_xcause_check(self, field, value):
        '''Function to verify the inputs for mcause.'''
        if (min(value) < 16):
            self._error(
                field, "Invalid platform specific values for exception cause.")

    def _check_with_key_check(self, field, value):
        if value['base']['type']['warl']['dependency_fields'] != []:
            par = re.split(
                "::", value['base']['type']['warl']['dependency_fields'][0])
            if not par[1] in value:
                self._error(field, " {} not present".format(par[1]))

    def _check_with_medeleg_reset(self, field, value):
        global supported_xlen
        s = format(value, '#{}b'.format(supported_xlen[0] + 2))
        if (s[-11:-10]) != '0' and value >= int("0x400", 16):
            self._error(field, " 11th bit must be hardwired to 0")

    def _check_with_sedeleg_reset(self, field, value):
        global supported_xlen
        s = format(value, '#{}b'.format(supported_xlen[0] + 2))
        if (s[-11:-8]) != '000' and value >= int("400", 16):
            self._error(field, " 11,10,9 bits should be hardwired to 0")

    def _check_with_vxsat_check(self, field, value):
        check = False
        xlen_str = 'rv32' if rv32 else 'rv64'
        global extension_list
        if 'Zpn' in extension_list and not value[xlen_str]['accessible']:
            self._error(field,f'[{xlen_str}] Field should be accessible since Zpn is present')
        if not 'Zpn' in extension_list and value[xlen_str]['accessible']:
            self._error(field,f'[{xlen_str}] Field should be accessible only when Zpn is present')
        if not 'Zpn' in extension_list and value[xlen_str]['ov']['implemented']:
            self._error(field, f'[{xlen_str}] Subfield ov should not be implemented since Zpn is not present')
        if 'Zpn' in extension_list and not value[xlen_str]['ov']['implemented']:
            self._error(field, f'[{xlen_str}] Subfield ov should be implemented since Zpn is present in isa')

