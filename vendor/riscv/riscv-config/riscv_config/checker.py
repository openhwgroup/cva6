import os
import logging
import copy
import re
import math

from cerberus import Validator

import itertools
import riscv_config.utils as utils
from riscv_config.errors import ValidationError
from riscv_config.schemaValidator import schemaValidator
import riscv_config.constants as constants
from riscv_config.warl import warl_class
from riscv_config.isa_validator import *

logger = logging.getLogger(__name__)


def reset():
    '''Function to set defaults to reset val of misa  based on presence of ISA extensions.'''
    global inp_yaml
    global extensions
    extension_enc = list("00000000000000000000000000")
    value=inp_yaml['ISA']
    global extension_list
    global ext_err
    global ext_err_list
    (extension_list, ext_err, ext_err_list) = get_extension_list(value)
    if "32" in value:
       xlen = 32
       ext = value[4:]
    elif "64" in value:
       xlen = 64
       ext = value[4:]
    elif "128" in value:
       xlen = 128
       ext = value[5:]
    for x in "ABCDEFHIJKLMNPQSTUVX":
            if (x in extension_list):
                extension_enc[25 - int(ord(x) - ord('A'))] = "1"
    extensions = int("".join(extension_enc), 2)
    ext_b=format(extensions, '#0{}b'.format(xlen+2))
    mxl='10'if xlen==64 else '01'
    ext_b = ext_b[:2] + str(mxl) + ext_b[4:]
    return int(ext_b, 2)

def resetsu():
    '''Function to set defaults to reset val of mstatus based on the xlen and S, U extensions'''
    global inp_yaml
    global extension_list
    if 64 in inp_yaml['supported_xlen'] and 'S' not in extension_list and 'U' in extension_list:
      return 8589934592
    elif 64 in inp_yaml['supported_xlen'] and 'U' in extension_list and 'S' in extension_list:
      return 42949672960
    else:
      return 0
def reset_vsstatus():
    '''Function to set defaults to reset val of mstatus based on the xlen and S, U extensions'''
    global inp_yaml
    global extension_list
    if 64 in inp_yaml['supported_xlen'] and 'U' in extension_list:
      return 8589934592
    else:
      return 0

def uset():
    '''Function to set defaults based on presence of 'U' extension.'''
    global extension_list
    if 'U' in extension_list:
        return {'implemented': True}
    else:
        return {'implemented': False}

def hset():
    '''Function to set defaults based on presence of 'U' extension.'''
    global extension_list
    if 'H' in extension_list:
        return {'implemented': True}
    else:
        return {'implemented': False}


def sset():
    '''Function to set defaults based on presence of 'S' extension.'''
    global extension_list
    if 'S' in extension_list:
        return {'implemented': True}
    else:
        return {'implemented': False}

def fsset():
    '''Function to set defaults based on presence of 'F' or 'S' extension.'''
    global extension_list
    if 'F' in extension_list or 'S' in extension_list:
        return {'implemented': True}
    else:
        return {'implemented': False}

def fset():
    '''Function to set defaults based on presence of 'F' extension.'''
    global extension_list
    if 'F' in extension_list:
        return {'implemented': True}
    else:
        return {'implemented': False}

def fregset():
    '''Function to set defaults based on presence of 'F' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'F' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
      if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True
    return temp

def uregset():
    '''Function to set defaults based on presence of 'U' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'U' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
      if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True
    return temp

def uregseth():
    '''Function to set defaults based on presence of 'U' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'U' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
    return temp

def hregseth():
    '''Function to set defaults based on presence of 'H' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'H' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
    return temp
def sregset():
    '''Function to set defaults based on presence of 'S' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'S' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
      if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True
    return temp

def nregset():
    '''Function to set defaults based on presence of 'N' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'N' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
      if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True
    return temp

def hregset():
    '''Function to set defaults based on presence of 'H' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'H' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
      if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True
    return temp

def sregseth():
    '''Function to set defaults based on presence of 'S' extension.'''
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'S' in extension_list:
      if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
    return temp


def nuset():
    '''Function to check and set defaults for all fields which are dependent on
        the presence of 'U' extension and 'N' extension.'''
    global extension_list
    if 'U' in extension_list and 'N' in extension_list:
        return {'implemented': True}
    else:
        return {'implemented': False}

def smrnmi_reset():
  global inp_yaml
  if 64 in inp_yaml['supported_xlen']:
    return 0x8000000000000000
  else:
    return 0x80000000

def smrnmi_set():
    '''Function to check and set defaults for all fields which are dependent on
        the presence of Smrnmi extension'''
    global inp_yaml
    global extension_list

    temp = { 'rv32': {'accessible': False},
             'rv64': {'accessible': False}
           }
    if 'Smrnmi' in extension_list:
        if 32 in inp_yaml['supported_xlen']:
            temp['rv32']['accessible'] = True
        else :
            temp['rv64']['accessible'] = True
    return temp

def pset():
    '''Function to check and set defaults for all fields which are dependent on
        the presence of P-SIMD sub-extension viz. zpn, zpsf, zbpbo'''
    global inp_yaml
    global extension_list

    temp = { 'rv32': {'accessible': False , 'ov': {'implemented': False}},
             'rv64': {'accessible': False , 'ov': {'implemented': False}}
           }
    if 'Zpn' in extension_list:
        if 32 in inp_yaml['supported_xlen']:
            temp['rv32']['accessible'] = True
            temp['rv32']['ov']['implemented'] = True
        else :
            temp['rv64']['accessible'] = True
            temp['rv64']['ov']['implemented'] = True
    return temp

def twset():
    '''Function to check and set value for tw field in misa.'''
    global extension_list
    if 'S' not in extension_list and 'U' not in extension_list:
        return {'implemented': False}
    else:
        return {'implemented': True}


def delegset():
    '''Function to set "implemented" value for mideleg regisrer.'''
    # return True
    global inp_yaml
    global extension_list
    var = True
    if 'S' not in extension_list and 'N' not in extension_list:
        var = False

    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True and var
    if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True and var
    return temp


def countset():
    global inp_yaml
    global extension_list
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 'S' in extension_list or 'U' in inp_yaml["ISA"]:
        if 32 in inp_yaml['supported_xlen']:
            temp['rv32']['accessible'] = True
        if 64 in inp_yaml['supported_xlen']:
            temp['rv64']['accessible'] = True
    return temp


def regset():
    global inp_yaml
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
    if 64 in inp_yaml['supported_xlen']:
        temp['rv64']['accessible'] = True
    return temp

def pmpregset():
    global inp_yaml
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    return temp

def pmpregseth():
    global inp_yaml
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    return temp

def counterhset():
    global inp_yaml
    temp = {'rv32': {'accessible': False}, 'rv64': {'accessible': False}}
    if 32 in inp_yaml['supported_xlen']:
        temp['rv32']['accessible'] = True
    return temp

def add_debug_setters(schema_yaml):
    '''Function to set the default setters for various fields in the debug schema'''
    regsetter = lambda doc: regset()

    tselectregsetter = lambda doc: pmpregset()
    schema_yaml['dcsr']['default_setter'] = regsetter
    schema_yaml['tselect']['default_setter'] = tselectregsetter
    schema_yaml['tinfo']['default_setter'] = tselectregsetter
    schema_yaml['hcontext']['default_setter'] = tselectregsetter
    schema_yaml['tdata1']['default_setter'] = tselectregsetter
    schema_yaml['tdata2']['default_setter'] = tselectregsetter
    schema_yaml['tdata3']['default_setter'] = tselectregsetter
    schema_yaml['tcontrol']['default_setter'] = tselectregsetter
    schema_yaml['scontext']['default_setter'] = tselectregsetter
    return schema_yaml

def add_reset_setters(schema_yaml):
    '''Function to set the default setters for extension  subfields in the misa'''
    global inp_yaml
    global extensions
    xlen=inp_yaml['supported_xlen'][0]
    rvxlen='rv'+str(xlen)
    extensions=hex(int(format(reset(), '#0{}b'.format(xlen+2))[(xlen-24):(xlen+2)], 2))
    schema_yaml['misa']['schema'][rvxlen]['schema']['extensions']['schema']['type']['default']['warl']['legal'][0]=schema_yaml['misa']['schema'][rvxlen]['schema']['extensions']['schema']['type']['default']['warl']['legal'][0].replace('0x3FFFFFFF', extensions)
    return schema_yaml

def add_fflags_type_setters(schema_yaml):
    global inp_yaml
    global extension_list
    xlen=inp_yaml['supported_xlen'][0]
    rvxlen='rv'+str(xlen)
    if 'F' not in extension_list:
        schema_yaml['fcsr']['schema'][rvxlen]['schema']['frm']['schema']['type']['default'] = {'ro_constant': 0}
        schema_yaml['fcsr']['schema'][rvxlen]['schema']['fflags']['schema']['type']['default'] = {'ro_constant': 0}
    return schema_yaml

def add_def_setters(schema_yaml):
    '''Function to set the default setters for various fields in the schema'''
    regsetter = lambda doc: regset()
    resetsetter=lambda doc: reset()
    reset_susetter=lambda doc: resetsu()
    reset_vsssetter=lambda doc: reset_vsstatus()
    pmpregsetter = lambda doc: pmpregset()
    counthsetter = lambda doc: counterhset()
    pmpreghsetter = lambda doc: pmpregseth()
    uregsetter = lambda doc: uregset()
    fregsetter = lambda doc: fregset()
    ureghsetter = lambda doc: uregseth()
    ssetter = lambda doc: sset()
    fssetter = lambda doc: fsset()
    fsetter = lambda doc: fset()
    sregsetter = lambda doc: sregset()
    nregsetter = lambda doc: nregset()
    hregsetter = lambda doc: hregset()
    hreghsetter = lambda doc: hregseth()
    sregsetterh = lambda doc: sregseth()
    nusetter = lambda doc: nuset()
    usetter = lambda doc: uset()
    hsetter = lambda doc: hset()
    twsetter = lambda doc: twset()
    delegsetter = lambda doc: delegset()
    psetter = lambda doc: pset()
    smrnmi_setter = lambda doc: smrnmi_set()
    reset_smrnmi_setter = lambda doc: smrnmi_reset()

    schema_yaml['sstatus']['default_setter'] = sregsetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['upie'][
        'default_setter'] = nusetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['upie'][
        'default_setter'] = nusetter

    schema_yaml['sstatus']['schema']['rv64']['schema']['uxl'][
        'default_setter'] = usetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['sie'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['sie'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['spie'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['spie'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['spp'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['spp'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['mxr'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['mxr'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['sum'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['sum'][
        'default_setter'] = ssetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['fs'][
        'default_setter'] = fssetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['fs'][
        'default_setter'] = fssetter
    schema_yaml['sstatus']['schema']['rv32']['schema']['sd'][
        'default_setter'] = fssetter
    schema_yaml['sstatus']['schema']['rv64']['schema']['sd'][
        'default_setter'] = fssetter
    schema_yaml['sie']['default_setter'] = sregsetter
    schema_yaml['sie']['schema']['rv32']['schema']['ueie'][
        'default_setter'] = nusetter
    schema_yaml['sie']['schema']['rv64']['schema']['ueie'][
        'default_setter'] = nusetter
    schema_yaml['sie']['schema']['rv32']['schema']['utie'][
        'default_setter'] = nusetter
    schema_yaml['sie']['schema']['rv64']['schema']['utie'][
        'default_setter'] = nusetter
    schema_yaml['sie']['schema']['rv32']['schema']['usie'][
        'default_setter'] = nusetter
    schema_yaml['sie']['schema']['rv64']['schema']['usie'][
        'default_setter'] = nusetter
    schema_yaml['sie']['schema']['rv32']['schema']['seie'][
        'default_setter'] = ssetter
    schema_yaml['sie']['schema']['rv64']['schema']['seie'][
        'default_setter'] = ssetter
    schema_yaml['sie']['schema']['rv32']['schema']['stie'][
        'default_setter'] = ssetter
    schema_yaml['sie']['schema']['rv64']['schema']['stie'][
        'default_setter'] = ssetter
    schema_yaml['sie']['schema']['rv32']['schema']['ssie'][
        'default_setter'] = ssetter
    schema_yaml['sie']['schema']['rv64']['schema']['ssie'][
        'default_setter'] = ssetter
    schema_yaml['sip']['default_setter'] = sregsetter
    schema_yaml['sip']['schema']['rv32']['schema']['ueip'][
        'default_setter'] = nusetter
    schema_yaml['sip']['schema']['rv64']['schema']['ueip'][
        'default_setter'] = nusetter
    schema_yaml['sip']['schema']['rv32']['schema']['utip'][
        'default_setter'] = nusetter
    schema_yaml['sip']['schema']['rv64']['schema']['utip'][
        'default_setter'] = nusetter
    schema_yaml['sip']['schema']['rv32']['schema']['usip'][
        'default_setter'] = nusetter
    schema_yaml['sip']['schema']['rv64']['schema']['usip'][
        'default_setter'] = nusetter
    schema_yaml['sip']['schema']['rv32']['schema']['seip'][
        'default_setter'] = ssetter
    schema_yaml['sip']['schema']['rv64']['schema']['seip'][
        'default_setter'] = ssetter
    schema_yaml['sip']['schema']['rv32']['schema']['stip'][
        'default_setter'] = ssetter
    schema_yaml['sip']['schema']['rv64']['schema']['stip'][
        'default_setter'] = ssetter
    schema_yaml['sip']['schema']['rv32']['schema']['ssip'][
        'default_setter'] = ssetter
    schema_yaml['sip']['schema']['rv64']['schema']['ssip'][
        'default_setter'] = ssetter
    schema_yaml['stvec']['default_setter'] = sregsetter
    schema_yaml['stvec']['schema']['rv32']['schema']['base'][
        'default_setter'] = ssetter
    schema_yaml['stvec']['schema']['rv64']['schema']['base'][
        'default_setter'] = ssetter
    schema_yaml['stvec']['schema']['rv32']['schema']['mode'][
        'default_setter'] = ssetter
    schema_yaml['stvec']['schema']['rv64']['schema']['mode'][
        'default_setter'] = ssetter

    schema_yaml['sepc']['default_setter'] = sregsetter
    schema_yaml['stval']['default_setter'] = sregsetter
    schema_yaml['scause']['default_setter'] = sregsetter
    schema_yaml['scause']['schema']['rv32']['schema']['interrupt'][
        'default_setter'] = ssetter
    schema_yaml['scause']['schema']['rv64']['schema']['interrupt'][
        'default_setter'] = ssetter
    schema_yaml['scause']['schema']['rv32']['schema']['exception_code'][
        'default_setter'] = ssetter
    schema_yaml['scause']['schema']['rv64']['schema']['exception_code'][
        'default_setter'] = ssetter
    schema_yaml['satp']['default_setter'] = sregsetter
    schema_yaml['satp']['schema']['rv32']['schema']['ppn'][
        'default_setter'] = ssetter
    schema_yaml['satp']['schema']['rv64']['schema']['ppn'][
        'default_setter'] = ssetter
    schema_yaml['satp']['schema']['rv32']['schema']['asid'][
        'default_setter'] = ssetter
    schema_yaml['satp']['schema']['rv64']['schema']['asid'][
        'default_setter'] = ssetter
    schema_yaml['satp']['schema']['rv32']['schema']['mode'][
        'default_setter'] = ssetter
    schema_yaml['satp']['schema']['rv64']['schema']['mode'][
        'default_setter'] = ssetter
    schema_yaml['sscratch']['default_setter'] = sregsetter

    schema_yaml['ustatus']['default_setter'] = nregsetter
    schema_yaml['ustatus']['schema']['rv32']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['ustatus']['schema']['rv64']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['ustatus']['schema']['rv32']['schema']['upie'][
        'default_setter'] = nusetter
    schema_yaml['ustatus']['schema']['rv64']['schema']['upie'][
        'default_setter'] = nusetter

    schema_yaml['uie']['default_setter'] = nregsetter
    schema_yaml['uie']['schema']['rv32']['schema']['ueie'][
        'default_setter'] = nusetter
    schema_yaml['uie']['schema']['rv64']['schema']['ueie'][
        'default_setter'] = nusetter
    schema_yaml['uie']['schema']['rv32']['schema']['utie'][
        'default_setter'] = nusetter
    schema_yaml['uie']['schema']['rv64']['schema']['utie'][
        'default_setter'] = nusetter
    schema_yaml['uie']['schema']['rv32']['schema']['usie'][
        'default_setter'] = nusetter
    schema_yaml['uie']['schema']['rv64']['schema']['usie'][
        'default_setter'] = nusetter
    schema_yaml['uip']['default_setter'] = nregsetter
    schema_yaml['uip']['schema']['rv32']['schema']['ueip'][
        'default_setter'] = nusetter
    schema_yaml['uip']['schema']['rv64']['schema']['ueip'][
        'default_setter'] = nusetter
    schema_yaml['uip']['schema']['rv32']['schema']['utip'][
        'default_setter'] = nusetter
    schema_yaml['uip']['schema']['rv64']['schema']['utip'][
        'default_setter'] = nusetter
    schema_yaml['uip']['schema']['rv32']['schema']['usip'][
        'default_setter'] = nusetter
    schema_yaml['uip']['schema']['rv64']['schema']['usip'][
        'default_setter'] = nusetter
    schema_yaml['utvec']['default_setter'] = nregsetter
    schema_yaml['utvec']['schema']['rv32']['schema']['base'][
        'default_setter'] = nusetter
    schema_yaml['utvec']['schema']['rv64']['schema']['base'][
        'default_setter'] = nusetter
    schema_yaml['utvec']['schema']['rv32']['schema']['mode'][
        'default_setter'] = nusetter
    schema_yaml['utvec']['schema']['rv64']['schema']['mode'][
        'default_setter'] = nusetter
    schema_yaml['uepc']['default_setter'] = nregsetter
    schema_yaml['utval']['default_setter'] = nregsetter
    schema_yaml['ucause']['default_setter'] = nregsetter
    schema_yaml['ucause']['schema']['rv32']['schema']['interrupt'][
        'default_setter'] = nusetter
    schema_yaml['ucause']['schema']['rv64']['schema']['interrupt'][
        'default_setter'] = nusetter
    schema_yaml['ucause']['schema']['rv32']['schema']['exception_code'][
        'default_setter'] = nusetter
    schema_yaml['ucause']['schema']['rv64']['schema']['exception_code'][
        'default_setter'] = nusetter
    schema_yaml['uscratch']['default_setter'] = nregsetter

    schema_yaml['fcsr']['schema']['rv32']['schema']['frm'][
        'default_setter'] = fsetter
    schema_yaml['fcsr']['schema']['rv64']['schema']['frm'][
        'default_setter'] = fsetter
    schema_yaml['fcsr']['schema']['rv32']['schema']['fflags'][
        'default_setter'] = fsetter
    schema_yaml['fcsr']['schema']['rv64']['schema']['fflags'][
        'default_setter'] = fsetter

    schema_yaml['misa']['default_setter'] = regsetter
    schema_yaml['misa']['schema']['reset-val']['default_setter'] = resetsetter
    schema_yaml['mstatus']['default_setter'] = regsetter
    schema_yaml['mstatus']['schema']['reset-val']['default_setter']=reset_susetter
    schema_yaml['vsstatus']['schema']['reset-val']['default_setter']=reset_vsssetter
    schema_yaml['mstatush']['default_setter'] = counthsetter
    schema_yaml['mvendorid']['default_setter'] = regsetter
    schema_yaml['mimpid']['default_setter'] = regsetter
    schema_yaml['marchid']['default_setter'] = regsetter
    schema_yaml['mhartid']['default_setter'] = regsetter
    schema_yaml['mtvec']['default_setter'] = regsetter
    schema_yaml['mip']['default_setter'] = regsetter
    schema_yaml['mie']['default_setter'] = regsetter
    schema_yaml['mscratch']['default_setter'] = regsetter
    schema_yaml['mepc']['default_setter'] = regsetter
    schema_yaml['mtval']['default_setter'] = regsetter
    schema_yaml['mtval2']['default_setter'] = hregsetter
    schema_yaml['mtinst']['default_setter'] = hregsetter
    schema_yaml['mcountinhibit']['default_setter'] = regsetter
    schema_yaml['mcycle']['default_setter'] = regsetter
    schema_yaml['minstret']['default_setter'] = regsetter
    schema_yaml['mcycleh']['default_setter'] = counthsetter
    schema_yaml['minstreth']['default_setter'] = counthsetter
    schema_yaml['pmpcfg0']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg1']['default_setter'] = pmpreghsetter
    schema_yaml['pmpcfg2']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg3']['default_setter'] = pmpreghsetter
    schema_yaml['pmpcfg4']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg5']['default_setter'] = pmpreghsetter
    schema_yaml['pmpcfg6']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg7']['default_setter'] = pmpreghsetter
    schema_yaml['pmpcfg8']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg9']['default_setter'] = pmpreghsetter
    schema_yaml['pmpcfg10']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg11']['default_setter'] = pmpreghsetter
    schema_yaml['pmpcfg12']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg13']['default_setter'] = pmpreghsetter
    schema_yaml['pmpcfg14']['default_setter'] = pmpregsetter
    schema_yaml['pmpcfg15']['default_setter'] = pmpreghsetter
    schema_yaml['pmpaddr0']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr1']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr2']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr3']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr4']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr5']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr6']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr7']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr8']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr9']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr10']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr11']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr12']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr13']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr14']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr15']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr16']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr17']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr18']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr19']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr20']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr21']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr22']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr23']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr24']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr25']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr26']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr27']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr28']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr29']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr30']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr31']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr32']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr33']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr34']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr35']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr36']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr37']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr38']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr39']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr40']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr41']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr42']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr43']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr44']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr45']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr46']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr47']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr48']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr49']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr50']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr51']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr52']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr53']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr54']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr55']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr56']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr57']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr58']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr59']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr60']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr61']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr62']['default_setter'] = pmpregsetter
    schema_yaml['pmpaddr63']['default_setter'] = pmpregsetter

    # event counters
    schema_yaml['mhpmevent3']['default_setter'] = regsetter
    schema_yaml['mhpmevent4']['default_setter'] = regsetter
    schema_yaml['mhpmevent5']['default_setter'] = regsetter
    schema_yaml['mhpmevent6']['default_setter'] = regsetter
    schema_yaml['mhpmevent7']['default_setter'] = regsetter
    schema_yaml['mhpmevent8']['default_setter'] = regsetter
    schema_yaml['mhpmevent9']['default_setter'] = regsetter
    schema_yaml['mhpmevent10']['default_setter'] = regsetter
    schema_yaml['mhpmevent11']['default_setter'] = regsetter
    schema_yaml['mhpmevent12']['default_setter'] = regsetter
    schema_yaml['mhpmevent13']['default_setter'] = regsetter
    schema_yaml['mhpmevent14']['default_setter'] = regsetter
    schema_yaml['mhpmevent15']['default_setter'] = regsetter
    schema_yaml['mhpmevent16']['default_setter'] = regsetter
    schema_yaml['mhpmevent17']['default_setter'] = regsetter
    schema_yaml['mhpmevent18']['default_setter'] = regsetter
    schema_yaml['mhpmevent19']['default_setter'] = regsetter
    schema_yaml['mhpmevent20']['default_setter'] = regsetter
    schema_yaml['mhpmevent21']['default_setter'] = regsetter
    schema_yaml['mhpmevent22']['default_setter'] = regsetter
    schema_yaml['mhpmevent23']['default_setter'] = regsetter
    schema_yaml['mhpmevent24']['default_setter'] = regsetter
    schema_yaml['mhpmevent25']['default_setter'] = regsetter
    schema_yaml['mhpmevent26']['default_setter'] = regsetter
    schema_yaml['mhpmevent27']['default_setter'] = regsetter
    schema_yaml['mhpmevent28']['default_setter'] = regsetter
    schema_yaml['mhpmevent29']['default_setter'] = regsetter
    schema_yaml['mhpmevent30']['default_setter'] = regsetter
    schema_yaml['mhpmevent31']['default_setter'] = regsetter

    schema_yaml['mhpmcounter3']['default_setter'] = regsetter
    schema_yaml['mhpmcounter4']['default_setter'] = regsetter
    schema_yaml['mhpmcounter5']['default_setter'] = regsetter
    schema_yaml['mhpmcounter6']['default_setter'] = regsetter
    schema_yaml['mhpmcounter7']['default_setter'] = regsetter
    schema_yaml['mhpmcounter8']['default_setter'] = regsetter
    schema_yaml['mhpmcounter9']['default_setter'] = regsetter
    schema_yaml['mhpmcounter10']['default_setter'] = regsetter
    schema_yaml['mhpmcounter11']['default_setter'] = regsetter
    schema_yaml['mhpmcounter12']['default_setter'] = regsetter
    schema_yaml['mhpmcounter13']['default_setter'] = regsetter
    schema_yaml['mhpmcounter14']['default_setter'] = regsetter
    schema_yaml['mhpmcounter15']['default_setter'] = regsetter
    schema_yaml['mhpmcounter16']['default_setter'] = regsetter
    schema_yaml['mhpmcounter17']['default_setter'] = regsetter
    schema_yaml['mhpmcounter18']['default_setter'] = regsetter
    schema_yaml['mhpmcounter19']['default_setter'] = regsetter
    schema_yaml['mhpmcounter20']['default_setter'] = regsetter
    schema_yaml['mhpmcounter21']['default_setter'] = regsetter
    schema_yaml['mhpmcounter22']['default_setter'] = regsetter
    schema_yaml['mhpmcounter23']['default_setter'] = regsetter
    schema_yaml['mhpmcounter24']['default_setter'] = regsetter
    schema_yaml['mhpmcounter25']['default_setter'] = regsetter
    schema_yaml['mhpmcounter26']['default_setter'] = regsetter
    schema_yaml['mhpmcounter27']['default_setter'] = regsetter
    schema_yaml['mhpmcounter28']['default_setter'] = regsetter
    schema_yaml['mhpmcounter29']['default_setter'] = regsetter
    schema_yaml['mhpmcounter30']['default_setter'] = regsetter
    schema_yaml['mhpmcounter31']['default_setter'] = regsetter

    schema_yaml['mhpmcounter3h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter4h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter5h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter6h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter7h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter8h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter9h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter10h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter11h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter12h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter13h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter14h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter15h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter16h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter17h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter18h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter19h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter20h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter21h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter22h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter23h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter24h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter25h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter26h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter27h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter28h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter29h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter30h']['default_setter'] = counthsetter
    schema_yaml['mhpmcounter31h']['default_setter'] = counthsetter
    schema_yaml['hpmcounter3']['default_setter'] = uregsetter
    schema_yaml['hpmcounter3h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter4']['default_setter'] = uregsetter
    schema_yaml['hpmcounter4h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter5']['default_setter'] = uregsetter
    schema_yaml['hpmcounter5h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter6']['default_setter'] = uregsetter
    schema_yaml['hpmcounter6h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter7']['default_setter'] = uregsetter
    schema_yaml['hpmcounter7h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter8']['default_setter'] = uregsetter
    schema_yaml['hpmcounter8h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter9']['default_setter'] = uregsetter
    schema_yaml['hpmcounter9h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter10']['default_setter'] = uregsetter
    schema_yaml['hpmcounter10h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter11']['default_setter'] = uregsetter
    schema_yaml['hpmcounter11h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter12']['default_setter'] = uregsetter
    schema_yaml['hpmcounter12h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter13']['default_setter'] = uregsetter
    schema_yaml['hpmcounter13h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter14']['default_setter'] = uregsetter
    schema_yaml['hpmcounter14h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter15']['default_setter'] = uregsetter
    schema_yaml['hpmcounter15h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter16']['default_setter'] = uregsetter
    schema_yaml['hpmcounter16h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter17']['default_setter'] = uregsetter
    schema_yaml['hpmcounter17h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter18']['default_setter'] = uregsetter
    schema_yaml['hpmcounter18h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter19']['default_setter'] = uregsetter
    schema_yaml['hpmcounter19h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter20']['default_setter'] = uregsetter
    schema_yaml['hpmcounter20h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter21']['default_setter'] = uregsetter
    schema_yaml['hpmcounter21h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter22']['default_setter'] = uregsetter
    schema_yaml['hpmcounter22h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter23']['default_setter'] = uregsetter
    schema_yaml['hpmcounter23h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter24']['default_setter'] = uregsetter
    schema_yaml['hpmcounter24h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter25']['default_setter'] = uregsetter
    schema_yaml['hpmcounter25h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter26']['default_setter'] = uregsetter
    schema_yaml['hpmcounter26h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter27']['default_setter'] = uregsetter
    schema_yaml['hpmcounter27h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter28']['default_setter'] = uregsetter
    schema_yaml['hpmcounter28h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter29']['default_setter'] = uregsetter
    schema_yaml['hpmcounter29h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter30']['default_setter'] = uregsetter
    schema_yaml['hpmcounter30h']['default_setter'] = ureghsetter
    schema_yaml['hpmcounter31']['default_setter'] = uregsetter
    schema_yaml['hpmcounter31h']['default_setter'] = ureghsetter

    schema_yaml['mcounteren']['default_setter'] = uregsetter
    schema_yaml['scounteren']['default_setter'] = uregsetter

    schema_yaml['mcause']['default_setter'] = regsetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['upie'][
        'default_setter'] = nusetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['upie'][
        'default_setter'] = nusetter

    schema_yaml['mstatus']['schema']['rv32']['schema']['mprv'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['mprv'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['uxl'][
        'default_setter'] = usetter
    schema_yaml['fflags']['default_setter'] = fregsetter
    schema_yaml['frm']['default_setter'] = fregsetter
    schema_yaml['fcsr']['default_setter'] = fregsetter
    schema_yaml['time']['default_setter'] = uregsetter
    schema_yaml['timeh']['default_setter'] = ureghsetter
    schema_yaml['cycle']['default_setter'] = uregsetter
    schema_yaml['cycleh']['default_setter'] = ureghsetter
    schema_yaml['instret']['default_setter'] = uregsetter
    schema_yaml['instreth']['default_setter'] = ureghsetter

    schema_yaml['mip']['schema']['rv32']['schema']['ueip'][
        'default_setter'] = nusetter
    schema_yaml['mip']['schema']['rv64']['schema']['ueip'][
        'default_setter'] = nusetter
    schema_yaml['mip']['schema']['rv32']['schema']['utip'][
        'default_setter'] = nusetter
    schema_yaml['mip']['schema']['rv64']['schema']['utip'][
        'default_setter'] = nusetter
    schema_yaml['mip']['schema']['rv32']['schema']['usip'][
        'default_setter'] = nusetter
    schema_yaml['mip']['schema']['rv64']['schema']['usip'][
        'default_setter'] = nusetter
    schema_yaml['mie']['schema']['rv32']['schema']['ueie'][
        'default_setter'] = nusetter
    schema_yaml['mie']['schema']['rv64']['schema']['ueie'][
        'default_setter'] = nusetter
    schema_yaml['mie']['schema']['rv32']['schema']['utie'][
        'default_setter'] = nusetter
    schema_yaml['mie']['schema']['rv64']['schema']['utie'][
        'default_setter'] = nusetter
    schema_yaml['mie']['schema']['rv32']['schema']['usie'][
        'default_setter'] = nusetter
    schema_yaml['mie']['schema']['rv64']['schema']['usie'][
        'default_setter'] = nusetter

    schema_yaml['mstatus']['schema']['rv32']['schema']['sie'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['sie'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['fs'][
        'default_setter'] = fssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['fs'][
        'default_setter'] = fssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['sd'][
        'default_setter'] = fssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['sd'][
        'default_setter'] = fssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['spie'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['spie'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['spp'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['spp'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['tvm'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['tvm'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['sxl'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['tsr'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['tsr'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['mxr'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['mxr'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv32']['schema']['sum'][
        'default_setter'] = ssetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['sum'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv32']['schema']['seip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv64']['schema']['seip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv32']['schema']['stip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv64']['schema']['stip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv32']['schema']['ssip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv64']['schema']['ssip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv32']['schema']['vssip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv64']['schema']['vssip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv32']['schema']['vstip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv64']['schema']['vstip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv32']['schema']['vseip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv64']['schema']['vseip'][
        'default_setter'] = ssetter
    schema_yaml['mip']['schema']['rv32']['schema']['sgeip'][
        'default_setter'] = hsetter
    schema_yaml['mip']['schema']['rv64']['schema']['sgeip'][
        'default_setter'] = hsetter
    schema_yaml['mie']['schema']['rv32']['schema']['seie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv64']['schema']['seie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv32']['schema']['stie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv64']['schema']['stie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv32']['schema']['ssie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv64']['schema']['ssie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv32']['schema']['vssie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv64']['schema']['vssie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv32']['schema']['vstie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv64']['schema']['vstie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv32']['schema']['vseie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv64']['schema']['vseie'][
        'default_setter'] = ssetter
    schema_yaml['mie']['schema']['rv32']['schema']['sgeie'][
        'default_setter'] = hsetter
    schema_yaml['mie']['schema']['rv64']['schema']['sgeie'][
        'default_setter'] = hsetter

    schema_yaml['mstatus']['schema']['rv32']['schema']['tw'][
        'default_setter'] = twsetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['tw'][
        'default_setter'] = twsetter
    schema_yaml['mstatush']['schema']['rv32']['schema']['gva'][
        'default_setter'] = hsetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['gva'][
        'default_setter'] = hsetter
    schema_yaml['mstatush']['schema']['rv32']['schema']['mpv'][
        'default_setter'] = hsetter
    schema_yaml['mstatus']['schema']['rv64']['schema']['mpv'][
        'default_setter'] = hsetter
    schema_yaml['medeleg']['default_setter'] = delegsetter
    schema_yaml['mideleg']['default_setter'] = delegsetter
    schema_yaml['sedeleg']['default_setter'] = nregsetter
    schema_yaml['sideleg']['default_setter'] = nregsetter

    schema_yaml['hstatus']['schema']['rv32']['schema']['gva'][
        'default_setter'] = hsetter
    schema_yaml['hstatus']['schema']['rv64']['schema']['gva'][
        'default_setter'] = hsetter
    schema_yaml['hstatus']['schema']['rv32']['schema']['spv'][
        'default_setter'] = hsetter
    schema_yaml['hstatus']['schema']['rv64']['schema']['spv'][
        'default_setter'] = hsetter
    schema_yaml['hstatus']['schema']['rv32']['schema']['spvp'][
        'default_setter'] = hsetter
    schema_yaml['hstatus']['schema']['rv64']['schema']['spvp'][
        'default_setter'] = hsetter
    schema_yaml['hstatus']['schema']['rv32']['schema']['hu'][
        'default_setter'] = hsetter
    schema_yaml['hstatus']['schema']['rv64']['schema']['hu'][
        'default_setter'] = hsetter

    schema_yaml['hstatus']['default_setter'] = hregsetter
    schema_yaml['hedeleg']['default_setter'] = hregsetter
    schema_yaml['hideleg']['default_setter'] = hregsetter
    schema_yaml['hie']['default_setter'] = hregsetter
    schema_yaml['hip']['default_setter'] = hregsetter
    schema_yaml['hvip']['default_setter'] = hregsetter
    schema_yaml['hgeip']['default_setter'] = hregsetter
    schema_yaml['hgeie']['default_setter'] = hregsetter
    schema_yaml['htval']['default_setter'] = hregsetter
    schema_yaml['htinst']['default_setter'] = hregsetter
    schema_yaml['hgatp']['default_setter'] = hregsetter
    schema_yaml['htimedelta']['default_setter'] = hregsetter
    schema_yaml['htimedeltah']['default_setter'] = hreghsetter
    schema_yaml['hcounteren']['default_setter'] = hregsetter

    schema_yaml['hie']['schema']['rv32']['schema']['sgeie'][
        'default_setter'] = hsetter
    schema_yaml['hie']['schema']['rv64']['schema']['sgeie'][
        'default_setter'] = hsetter
    schema_yaml['hip']['schema']['rv32']['schema']['sgeip'][
        'default_setter'] = hsetter
    schema_yaml['hip']['schema']['rv64']['schema']['sgeip'][
        'default_setter'] = hsetter

    schema_yaml['vsstatus']['default_setter'] = hregsetter
    schema_yaml['vsstatus']['schema']['rv32']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['vsstatus']['schema']['rv64']['schema']['uie'][
        'default_setter'] = nusetter
    schema_yaml['vsstatus']['schema']['rv32']['schema']['upie'][
        'default_setter'] = nusetter
    schema_yaml['vsstatus']['schema']['rv64']['schema']['upie'][
        'default_setter'] = nusetter

    schema_yaml['vsstatus']['schema']['rv64']['schema']['uxl'][
        'default_setter'] = usetter
    schema_yaml['vsstatus']['schema']['rv32']['schema']['sie'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv64']['schema']['sie'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv32']['schema']['spie'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv64']['schema']['spie'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv32']['schema']['spp'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv64']['schema']['spp'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv32']['schema']['mxr'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv64']['schema']['mxr'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv32']['schema']['sum'][
        'default_setter'] = ssetter
    schema_yaml['vsstatus']['schema']['rv64']['schema']['sum'][
        'default_setter'] = ssetter
    schema_yaml['vsie']['default_setter'] = hregsetter
    schema_yaml['vsie']['schema']['rv32']['schema']['seie'][
        'default_setter'] = ssetter
    schema_yaml['vsie']['schema']['rv64']['schema']['seie'][
        'default_setter'] = ssetter
    schema_yaml['vsie']['schema']['rv32']['schema']['stie'][
        'default_setter'] = ssetter
    schema_yaml['vsie']['schema']['rv64']['schema']['stie'][
        'default_setter'] = ssetter
    schema_yaml['vsie']['schema']['rv32']['schema']['ssie'][
        'default_setter'] = ssetter
    schema_yaml['vsie']['schema']['rv64']['schema']['ssie'][
        'default_setter'] = ssetter
    schema_yaml['vsip']['default_setter'] = hregsetter
    schema_yaml['vsip']['schema']['rv32']['schema']['seip'][
        'default_setter'] = ssetter
    schema_yaml['vsip']['schema']['rv64']['schema']['seip'][
        'default_setter'] = ssetter
    schema_yaml['vsip']['schema']['rv32']['schema']['stip'][
        'default_setter'] = ssetter
    schema_yaml['vsip']['schema']['rv64']['schema']['stip'][
        'default_setter'] = ssetter
    schema_yaml['vsip']['schema']['rv32']['schema']['ssip'][
        'default_setter'] = ssetter
    schema_yaml['vsip']['schema']['rv64']['schema']['ssip'][
        'default_setter'] = ssetter
    schema_yaml['vstvec']['default_setter'] = hregsetter
    schema_yaml['vsepc']['default_setter'] = hregsetter
    schema_yaml['vstval']['default_setter'] = hregsetter
    schema_yaml['vscause']['default_setter'] = hregsetter
    schema_yaml['vsatp']['default_setter'] = hregsetter
    schema_yaml['vsscratch']['default_setter'] = hregsetter
    schema_yaml['vxsat']['default_setter'] = psetter
    schema_yaml['mnscratch']['default_setter'] = smrnmi_setter
    schema_yaml['mnepc']['default_setter'] = smrnmi_setter
    schema_yaml['mnstatus']['default_setter'] = smrnmi_setter
    schema_yaml['mncause']['default_setter'] = smrnmi_setter
    schema_yaml['mncause']['schema']['reset-val']['default_setter'] = reset_smrnmi_setter
    return schema_yaml


def trim(foo):
    '''
        Function to trim the dictionary. Any node with implemented field set to false is trimmed of all the other nodes.

        :param foo: The dictionary to be trimmed.

        :type foo: dict

        :return: The trimmed dictionary.
    '''
    keys = foo.keys()
    if 'rv32' in keys:
        if not foo['rv32']['accessible']:
            foo['rv32'] = {'accessible': False}
    if 'rv64' in keys:
        if not foo['rv64']['accessible']:
            foo['rv64'] = {'accessible': False}
    if 'implemented' in keys:
        if not foo['implemented']:
            temp = foo
            for k in list(
                    set(foo.keys()) -
                    set(['description', 'msb', 'lsb', 'implemented', 'shadow', 'shadow_type'])
            ):
                try:
                    temp.pop(k)
                except KeyError:
                    continue
            return temp
    for key in keys:
        if isinstance(foo[key], dict):
            t = trim(foo[key])
            foo[key] = t
    return foo


def groupc(test_list):
    ''' Generator function to squash consecutive numbers for wpri bits.'''
    for x, y in itertools.groupby(enumerate(test_list), lambda a: a[1] - a[0]):
        y = list(y)
        a = y[0][1]
        b = y[-1][1]
        if a == b:
            yield [a]
        else:
            yield [a, b]


def get_fields(node, bitwidth):
    fields = list(
        set(node.keys()) -
        set(['fields', 'msb', 'lsb', 'accessible', 'shadow', 'shadow_type','type']))

    if not fields:
        return fields
    nf = {}
    for x in fields:
        nf[x] = node[x]['lsb']
    nf = sorted(nf.items(), key=lambda x: x[1], reverse=False)
    nfields=[]
    for k, v in nf:
        nfields.append(k)

    fields = nfields
    bits = set(range(bitwidth))
    for entry in fields:
        bits -= set(range(node[entry]['lsb'], node[entry]['msb'] + 1))
    bits = list(groupc(sorted(list(bits))))
    if not bits:
        return fields
    else:
        fields.append(bits)
        return fields

def update_fields(spec, logging=False):
    for csrname, csrnode in spec.items():
        if isinstance(csrnode, dict) and 'priv_mode' in csrnode:
            if 'indexing_reg' in csrnode:
                continue
            if csrnode['rv32']['accessible']:
                csrnode['rv32']['fields'] = get_fields(
                    csrnode['rv32'], 32)
            if csrnode['rv64']['accessible']:
                csrnode['rv64']['fields'] = get_fields(
                    csrnode['rv64'], 64)
    return spec

def check_fields(spec):
    errors = {}
    for csr, node, in spec.items() :
         fault_node = node
         error=[]
         if csr.startswith('uarch_'):
             continue
         if node['rv32']['accessible']:
                node['rv32']['fields'] = get_fields(node['rv32'], 32)
         if node['rv64']['accessible']:
                node['rv64']['fields'] = get_fields(node['rv64'], 64)
         fields = list(set(['rv32', 'rv64', 'description', 'address', 'priv_mode', 'reset-val']) - set(node.keys()) )
         if fields:
            error.append("The fields " + "".join(fields) + " are missing")
         if node['rv32']['accessible']:
            if any(type(e)==list for e in node['rv32']['fields']):
             sub_fields = node['rv32']['fields'][:-1]
            else:
             sub_fields = node['rv32']['fields']
            if not sub_fields :
             subfields = list(set(['msb', 'lsb', 'accessible', 'shadow', 'shadow_type', 'fields', 'type']) - set(node['rv32'].keys()) )
             if subfields:
                error.append("The subfield " + "".join(subfields) + " are not present")
            else:
              for x in sub_fields :
                subfields = list(set(['msb', 'lsb', 'implemented', 'description', 'shadow', 'shadow_type', 'type']) - set(node['rv32'][x].keys()) )
                if subfields :
                   error.append("The subfields " + "".join(subfields) + " are not present in " + str(x))
         if node['rv64']['accessible']:
            if any(type(e)==list for e in node['rv64']['fields']):
             sub_fields = node['rv64']['fields'][:-1]
            else:
             sub_fields = node['rv64']['fields']
            if not sub_fields :
             subfields = list(set(['msb', 'lsb', 'accessible', 'fields', 'shadow', 'shadow_type', 'type']) - set(node['rv64'].keys()))
             if subfields:
                error.append("The subfield " + "".join(subfields) + " are not present")
            else:
              for x in sub_fields :
                subfields = list(set(['msb', 'lsb', 'implemented', 'description', 'shadow', 'shadow_type', 'type']) - set(node['rv64'][x].keys()) )
                if subfields :
                   error.append("The subfields " + "".join(subfields) + " are not present in " + str(x))
         if bin(node['address'])[2:][::-1][6:8] != '11' and bin(node['address'])[2:][::-1][8:12] != '0001':
             error.append('Address is not in custom csr ranges')
         if (bin(node['address'])[2:][::-1][8:10] == '00' and node['priv_mode'] != 'U' ) or (bin(node['address'])[2:][::-1][8:10] == '01' and node['priv_mode'] != 'S' ) or (bin(node['address'])[2:][::-1][8:10] == '11' and node['priv_mode'] != 'M') :
            error.append('Privilege does not match with the address')
         if error:
            errors[csr] = error
    return errors
def check_shadows(spec, logging = False):
    ''' Check if the shadowed fields are implemented and of the same size as the
    source'''
    errors = {}
    _rvxlen = ['rv32', 'rv64']
    for csr, content in spec.items():
        if logging:
            logger.debug('Checking Shadows for ' + csr)
        error = []
        if isinstance(content, dict) and 'description' in content:
            if 'indexing_reg' in content:
                continue
            for rvxlen in _rvxlen:
                if content[rvxlen]['accessible'] and not content[rvxlen]['fields']:
                    if content[rvxlen]['shadow'] is None:
                        continue
                    else:
                        shadow = content[rvxlen]['shadow'].split('.')
                        if len(shadow) > 2:
                            error.append('Shadow field of should only up to 1 dot')
                            continue
                        elif len(shadow) == 2:
                            scsr = shadow[0]
                            subscsr = shadow[1]
                            if not spec[scsr][rvxlen][subscsr]['implemented']:
                                error.append(' Shadow field ' + scsr + '.' +\
                                            subscsr + ' not implemented')
                                continue
                            scsr_size = spec[scsr][rvxlen][subscsr]['msb'] -\
                                    spec[scsr][rvxlen][subscsr]['lsb']
                            csr_size = spec[csr][rvxlen]['msb'] - spec[csr][rvxlen]['lsb']
                            if scsr_size != csr_size :
                                error.append('Shadow field '+ \
                                        scsr + '.' + subscsr + \
                                        ' does not match in size')
                        else:
                            scsr = shadow[0]
                            if not spec[scsr][rvxlen]['accessible']:
                                error.append('Shadow field ' + scsr + ' not implemented')
                                continue
                            scsr_size = spec[scsr][rvxlen]['msb'] - spec[scsr][rvxlen]['lsb']
                            csr_size = spec[csr][rvxlen]['msb'] - spec[csr][rvxlen]['lsb']
                            if scsr_size != csr_size :
                                error.append('Shadow field '+ scsr +\
                                        'does not match in size')
                elif content[rvxlen]['accessible']:
                    for subfield in content[rvxlen]['fields']:
                        if isinstance(subfield ,list):
                            continue
                        if content[rvxlen][subfield]['shadow'] is None:
                           continue
                        elif content[rvxlen][subfield]['implemented']:
                            shadow = content[rvxlen][subfield]['shadow'].split('.')
                            if len(shadow) > 2:
                                error.append('Shadow field of should only up to 1 dot')
                                continue
                            elif len(shadow) == 1:
                                scsr = shadow[0]
                                if not spec[scsr][rvxlen]['accessible']:
                                    error.append('Subfield ' + subfield + \
                                        ' shadowing ' + scsr + ' not implemented')
                                    continue
                                scsr_size = spec[scsr][rvxlen]['msb'] - spec[scsr][rvxlen]['lsb']
                                csr_size = spec[csr][rvxlen][subfield]['msb'] -\
                                        spec[csr][rvxlen][subfield]['lsb']
                                if scsr_size != csr_size :
                                    error.append('Subfield ' + subfield +'shadowing'+ \
                                            scsr + ' does not match in size')
                            else:
                                scsr = shadow[0]
                                subscsr = shadow[1]
                                if not spec[scsr][rvxlen][subscsr]['implemented']:
                                    error.append('Subfield ' + subfield + \
                                            ' shadowing ' + scsr + '.' +\
                                            subscsr + ' not implemented')
                                    continue
                                scsr_size = spec[scsr][rvxlen][subscsr]['msb'] -\
                                        spec[scsr][rvxlen][subscsr]['lsb']
                                csr_size = spec[csr][rvxlen][subfield]['msb'] -\
                                        spec[csr][rvxlen][subfield]['lsb']
                                if scsr_size != csr_size :
                                    error.append('Subfield ' + subfield +'shadowing'+ \
                                            scsr + '.' + subscsr + \
                                            ' does not match in size')

        if error:
            errors[csr] = error
    return errors

def check_mhpm(spec, logging = False):
    ''' Check if the mhpmcounters and corresponding mhpmevents are implemented and of the same size as the
    source'''
    errors = {}
    for csrname, content, in spec.items():
        error = []
        if 'mhpmcounter' in csrname:
            index = int(re.findall('\d+',csrname.lower())[0])
            if content['rv64']['accessible'] :
                if not spec['mhpmevent'+str(index)]['rv64']['accessible']:
                    error.append(csrname + " counter doesn't have the corresponding mhpmevent register accessible")
            if content['rv32']['accessible'] :
                if not spec['mhpmevent'+str(index)]['rv32']['accessible']:
                    error.append(csrname + " counter doesn't have the corresponding mhpmevent register accessible")
        if 'mhpmevent' in csrname:
            index = int(re.findall('\d+',csrname.lower())[0])
            if content['rv64']['accessible'] :
                if not spec['mhpmcounter'+str(index)]['rv64']['accessible']:
                    error.append(csrname + " event reg doesn't have the corresponding mhpmcounter register accessible")
            if content['rv32']['accessible'] :
                if not spec['mhpmcounter'+str(index)]['rv32']['accessible']:
                    error.append(csrname + " event reg doesn't have the corresponding mhpmcounter register accessible")
            if content['rv32']['accessible'] :
                if not spec['mhpmcounter'+str(index)+'h']['rv32']['accessible']:
                    error.append(csrname + " event reg doesn't have the corresponding mhpmcounter 'h' counterpart register accessible")
        if error:
            errors[csrname] = error
    return errors

def check_supervisor(spec, logging=False):
    ''' this function includes several supervisor related checks:

    - check if pte_ad_hw_update is True, then satp.mode should be able to take
      one of the possible virtualization modes
    '''
    errors = {}

    pte_ad_hw_update = spec['pte_ad_hw_update']
    xlen = 64 if 64 in spec['supported_xlen'] else 32
    msb = 63 if xlen == 64 else 31
    lsb = 60 if xlen == 64 else 31
    virt_modes = [1] if xlen == 32 else [8,9,10,11]
    if spec['satp'][f'rv{xlen}']['accessible']: # perform satp checks only if it is accessible
        satp_mode_impl = spec['satp'][f'rv{xlen}']['mode']['implemented']
        satp_mode_type = spec['satp'][f'rv{xlen}']['mode']['type']
        virtualization_possible = False
        if 'ro_constant' in satp_mode_type:
            if satp_mode_type['ro_constant'] == 0:
                virtualization_possible = False
            else:
                virtualization_possible = True
        elif 'warl' in satp_mode_type:
            # these are the checks from _check_with_satp_modes64
            if xlen == 64:
                warl_inst = warl_class(satp_mode_type['warl'], 'satp::mode',63, 60)
                for x in [1,2,3,4,5,6,7,11,12,13]:
                    err = warl_inst.islegal(x)
                    if not err:
                        errors['satp_mode_checks'] = f'warl function for satp::mode accepts \
        "{x}" as a legal value - which is incorrect'
            warl_inst = warl_class(satp_mode_type['warl'], 'satp::mode', msb, lsb, spec)
            for x in virt_modes:
                err = warl_inst.islegal(x)
                if not err:
                    virtualization_possible = True
                    break

    if pte_ad_hw_update and not virtualization_possible:
        errors['pte_ad_hw_update'] = ['pte_ad_hw_update should be True only if satp.mode can be \
set to one of the legal virtualization modes']
    return errors



def check_pmp(spec, logging = False):
    ''' Check if the pmp csrs are implemented correctly as per spec. The
    following checks are performed:

        - the number of accessible pmpaddr csrs must be 0, 16 or 64
        - the number of implemented pmpcfg csrs must be 0, 16 or 64
        - the pmpaddr and pmpcfgs must be implemented implemented from the
          lowest numbered indices and be contiguous
        - the number of accessible pmpaddr csrs and the implemented pmpcfg csrs
          must be the same
        - for each accesible pmpaddr csr the corresponding pmpcfg csr must be
          implemented
        - reset values of the accessible pmpaddr csrs must be coherent with the
          pmp_granularity field.
    '''
    logger.info('Performing Checks on PMP CSRs')
    errors = {}
    isa = 'rv32' if '32' in spec['ISA'] else 'rv64'
    pmpaddr_count = 0
    pmpcfg_count = 0
    pmpaddr_reg = []
    pmpcfg_reg = []
    for x in range(64):
        if spec[f'pmpaddr{x}'][isa]['accessible']:
            pmpaddr_count += 1
            pmpaddr_reg.append(x)
        if '32' in isa:
            index = int(x/4)
        else:
            index = int(x/8)*2
        if spec[f'pmpcfg{index}'][isa]['accessible']:
            if spec[f'pmpcfg{index}'][isa][f'pmp{x}cfg']['implemented']:
                pmpcfg_count += 1
                pmpcfg_reg.append(x)

    logger.debug(f'pmpaddr_count={pmpaddr_count}')
    logger.debug(f'pmpcfg_count={pmpcfg_count}')

    if pmpaddr_count != 0 and pmpaddr_reg != list(range(0,max(pmpaddr_reg)+1)):
        errors['PMP-ADDR'] = [f' the lowest-numbered PMP-ADDR CSRs must be \
implemented first starting with 0. Found : {pmpaddr_reg}']
    if pmpcfg_count!= 0 and pmpcfg_reg != list(range(0,max(pmpcfg_reg)+1)):
        errors['PMP-CFG'] = [f' the lowest-numbered PMP-CFG CSRs must be \
implemented first starting with 0. Found : {pmpcfg_reg}']

    if pmpaddr_count not in [0, 16, 64]:
        errors["PMP-ADDR"] = [f'The number of accessible PMPADDR* registers \
must be 0, 16 or 64. But found {pmpaddr_count}']
    if pmpcfg_count not in [0, 16, 64]:
        errors["PMP-CFG"] = [f'The number of implemented PMP*CGF registers \
must be 0, 16 or 64. But found {pmpcfg_count}']
    if pmpcfg_count != pmpaddr_count:
        errors["PMP"] = [f' the number of pmpaddr* csrs [{pmpaddr_count}]and \
pmp*cfg registers [{pmpcfg_count}] do not match']

    for csrname, content, in spec.items():
        error = []
        Grain=int(spec['pmp_granularity'])
        if 'pmpaddr' in csrname:
            index = int(re.findall('\d+',csrname.lower())[0])
            if content['rv64']['accessible'] :
                reset_val_addr = (bin(content['reset-val'])[2:].zfill(64))[::-1]
                reset_val_cfg  = (bin(spec['pmpcfg'+str(int(int(index/8)*2))]['reset-val'])[2:].zfill(64))[::-1]
                if not spec['pmpcfg'+str(int(int(index/8)*2))]['rv64']['accessible']:
                    error.append(csrname + " addr doesn't have the corresponding pmp config register accessible")
                if not spec['pmpcfg'+str(int(int(index/8)*2))]['rv64']['pmp'+str(index)+'cfg']['implemented'] :
                    error.append(csrname + " addr doesn't have the corresponding pmpcfg" +str(int(index/4)) + "_pmp" + str(index) +"cfg register implemented")
                if reset_val_cfg[8*(index-(int(index/8)*8)) + 4] == '1' and Grain >=2 :     #NAPOT, Bit A of pmpXcfg is set
                  if '0' in reset_val_addr[0:(Grain-1)] or (reset_val_addr[Grain-1] != '0') :
                    error.append(csrname + 'reset value does not adhere with the pmp granularity')
                elif Grain >= 1: #TOR
                  if int(content['reset-val']) % (2**Grain) != 0 :
                    error.append(csrname + 'reset value does not adhere with the pmp granularity')
            if content['rv32']['accessible'] :
                reset_val_addr = (bin(content['reset-val'])[2:].zfill(32))[::-1]
                reset_val_cfg  = (bin(spec['pmpcfg'+str(int(index/4))]['reset-val'])[2:].zfill(32))[::-1]
                if not spec['pmpcfg'+str(int(index/4))]['rv32']['accessible']:
                    error.append(csrname + " addr doesn't have the corresponding pmp config register accessible")
                if not spec['pmpcfg'+str(int(index/4))]['rv32']['pmp'+str(index)+'cfg']['implemented'] :
                    error.append(csrname + " addr doesn't have the corresponding pmpcfg" +str(int(index/4)) + "_pmp" + str(index) +"cfg register implemented")
                if reset_val_cfg[8*(index-(int(index/4)*4)) + 4] == '1' and Grain >=2 :     #NAPOT, Bit A of pmpXcfg is set
                 if '0' in reset_val_addr[0:(Grain-1)] or (reset_val_addr[Grain-1] != '0') :
                    error.append(csrname + 'reset value does not adhere with the pmp granularity')
                elif Grain >= 1: #TOR
                  if int(content['reset-val']) % (2**Grain) != 0 :
                    error.append(csrname + 'reset value does not adhere with the pmp granularity')
        if 'pmpcfg' in csrname:
            if content['rv64']['accessible'] :
                for subfield in content['rv64']['fields']:
                 index = int(re.findall('\d+',subfield)[0])
                 if content['rv64'][subfield]['implemented'] and not spec['pmpaddr'+str(index)]['rv64']['accessible']:
                    error.append(csrname + "_" + subfield + " doesn't have the corresponding pmpaddr accessible")
            if content['rv32']['accessible'] :
                for subfield in content['rv32']['fields']:
                 index = int(re.findall('\d+',subfield)[0])
                 if content['rv32'][subfield]['implemented'] and not spec['pmpaddr'+str(index)]['rv32']['accessible']:
                    error.append(csrname + "_" + subfield + " doesn't have the corresponding pmpaddr accessible")
        if error:
            errors[csrname] = error
    return errors

def check_warl_legality(spec, logging = False):
    errors = {}
    warlnodes = {}
    xlen = 64 if 64 in spec['supported_xlen'] else 32
    for csrname, csrnode in spec.items():
        logger.debug(f'Checking legality of warl strings for csr: {csrname}')
        # don't perform any warl legality checks for uarch signal definitions.
        if csrname == 'uarch_signals':
            continue
        if isinstance(csrnode, dict) and 'priv_mode' in csrnode:
            if csrnode[f'rv{xlen}']['accessible']:
                if 'indexing_reg' in csrnode:
                    for n in csrnode[f'rv{xlen}']['index_list']:
                        _csrname = f'{csrname}[{n["index_val"]}]'
                        if 'warl' in n['type'] and n['shadow'] is None:
                            warlnodes[_csrname] = {}
                            warlnodes[_csrname]['warl'] = n['type']['warl']
                            warlnodes[_csrname]['msb'] = csrnode[f'rv{xlen}']['msb']
                            warlnodes[_csrname]['lsb'] = csrnode[f'rv{xlen}']['lsb']
                elif csrnode[f'rv{xlen}']['fields'] == []:
                    if csrnode[f'rv{xlen}']['shadow'] is None and \
                            'warl' in csrnode[f'rv{xlen}']['type']:
                        warlnodes[csrname] = {}
                        warlnodes[csrname]['warl'] = csrnode[f'rv{xlen}']['type']['warl']
                        warlnodes[csrname]['msb'] = csrnode[f'rv{xlen}']['msb']
                        warlnodes[csrname]['lsb'] = csrnode[f'rv{xlen}']['lsb']
                else:
                    for f in csrnode[f'rv{xlen}']['fields']:
                        if not isinstance(f, list) and csrnode[f'rv{xlen}'][f]['implemented']:
                            if csrnode[f'rv{xlen}'][f]['shadow'] is None and \
                                    'warl' in csrnode[f'rv{xlen}'][f]['type']:
                                warlnodes[f'{csrname}::{f}'] = {}
                                warlnodes[f'{csrname}::{f}']['warl'] = csrnode[f'rv{xlen}'][f]['type']['warl']
                                warlnodes[f'{csrname}::{f}']['msb'] = csrnode[f'rv{xlen}'][f]['msb']
                                warlnodes[f'{csrname}::{f}']['lsb'] = csrnode[f'rv{xlen}'][f]['lsb']

    for csrname, node in warlnodes.items():
        if logging:
            logger.debug(f'Checking legality of warl strings for csr: {csrname}')
        err = []
        warl_inst = warl_class(node['warl'], csrname, node['msb'],node['lsb'], spec)
        err_f = warl_inst.iserr()
        if err_f:
            errors[csrname] = err_f

    return errors

def check_reset(spec, logging=False):
    errors = {}
    resetnodes = {}
    xlen = 64 if 64 in spec['supported_xlen'] else 32
    for csrname, csrnode in spec.items():
        if isinstance(csrnode, dict) and 'priv_mode' in csrnode:
            if csrnode[f'rv{xlen}']['accessible']:
                if 'indexing_reg' in csrnode:
                    for n in csrnode[f'rv{xlen}']['index_list']:
                        csrn = f'{csrname}[{n["index_val"]}]'
                        if n['shadow'] is None:
                            resetnodes[csrn] = {}
                            resetnodes[csrn]['type'] = n['type']
                            resetnodes[csrn]['msb'] = csrnode[f'rv{xlen}']['msb']
                            resetnodes[csrn]['lsb'] = csrnode[f'rv{xlen}']['lsb']
                            resetnodes[csrn]['val'] = n['reset-val']
                elif csrnode[f'rv{xlen}']['fields'] == [] and csrnode[f'rv{xlen}']['shadow'] is None:
                    csr_reset_val = csrnode['reset-val']
                    resetnodes[csrname] = {}
                    resetnodes[csrname]['type'] = csrnode[f'rv{xlen}']['type']
                    resetnodes[csrname]['val'] = csr_reset_val
                    resetnodes[csrname]['msb'] = csrnode[f'rv{xlen}']['msb']
                    resetnodes[csrname]['lsb'] = csrnode[f'rv{xlen}']['lsb']
                elif csrnode[f'rv{xlen}']['fields']:
                    csr_reset_val = csrnode['reset-val']
                    for f in csrnode[f'rv{xlen}']['fields']:
                        if not isinstance(f, list) and csrnode[f'rv{xlen}'][f]['implemented']:
                            if csrnode[f'rv{xlen}'][f]['shadow'] is None:
                                submsb = csrnode[f'rv{xlen}'][f]['msb']
                                sublsb = csrnode[f'rv{xlen}'][f]['lsb']
                                subbitlen = submsb - sublsb + 1
                                resetnodes[f'{csrname}::{f}'] = {}
                                resetnodes[f'{csrname}::{f}']['val'] = \
                                        (csr_reset_val >> sublsb) & ((1<<subbitlen)-1)
                                resetnodes[f'{csrname}::{f}']['msb'] = submsb
                                resetnodes[f'{csrname}::{f}']['lsb'] = sublsb
                                resetnodes[f'{csrname}::{f}']['type'] = csrnode[f'rv{xlen}'][f]['type']
                        elif isinstance(f, list):
                            for entry in f:
                                low = entry[0]
                                high = entry[-1]
                                bitlen = high - low + 1
                                test_val = (csr_reset_val >> low) & ((1<<bitlen)-1)
                                if test_val != 0:
                                    errors[csrname] = [f'WPRI bits [{high}:{low}] should \
be zero']

    for csrname, csrnode in resetnodes.items():
        error = []
        logger.debug(f'-- Checking reset values for csr: {csrname}')
        error = check_values_in_type(csrname, csrnode, spec, logging)
        if error:
            errors[csrname]= error
    return errors

def check_values_in_type(csrname, csrnode, spec, logging=False):
    error = []
    val = csrnode['val']
    if 'wlrl' in csrnode['type']:
        wlrl_atleast_one_pass = False
        for entry in csrnode['type']['wlrl']:
            if ":" in entry:
                [low, high] = [ int(x,0) for x in entry.split(":")]
                if val >= low and val <= high:
                    wlrl_atleast_one_pass = True
                    break
            elif val == int(entry, 0):
                wlrl_atleast_one_pass = True
                break
        if not wlrl_atleast_one_pass:
            error.append(f"Reset value:{hex(val)} \
doesn't match the 'wlrl' description :{csrnode['type']['wlrl']} for the register.")
    elif 'ro_constant' in csrnode['type']:
        if val != csrnode['type']['ro_constant']:
            error.append("Reset value doesnt match the \
'ro_constant' description for the register.")
    elif 'ro_variable' in csrnode['type']:
        pass
    elif "warl" in csrnode['type']:
        warl_inst = warl_class(csrnode['type']['warl'], f'{csrname}', csrnode['msb'], csrnode['lsb'], spec)
        legal_err = warl_inst.islegal(val)
        if legal_err != []:
            error.append( f" value:{val} doesn't match the 'warl' description for the register {csrname}.")
            error = error + legal_err
    return error


def check_indexing(spec, logging = False):
    errors = {}
    xlen = 64 if 64 in spec['supported_xlen'] else 32
    for csrname, csrnode in spec.items():
        if isinstance(csrnode, dict) and 'priv_mode' in csrnode:
            if csrnode[f'rv{xlen}']['accessible']:
                if 'indexing_reg' in csrnode:
                    logger.debug(f'-- Checking legality of indexed register {csrname}')
                    indexing_reg = csrnode[f'rv{xlen}']['index_select_reg']
                    if not spec[indexing_reg][f'rv{xlen}']['accessible']:
                        errors[csrname] = [f'For csr:{csrname} the indexing_reg {indexing_reg} is not accessible']
                    else:
                        index_val_list = []
                        for n in csrnode[f'rv{xlen}']['index_list']:
                            value_for_indexing_reg = n['index_val']
                            logger.debug(f'--- Checking if index value: {value_for_indexing_reg} is legal for indexing register : {indexing_reg} ')
                            valuenode = {}
                            valuenode['msb'] = spec[indexing_reg][f'rv{xlen}']['msb']
                            valuenode['lsb'] = spec[indexing_reg][f'rv{xlen}']['lsb']
                            valuenode['val'] = value_for_indexing_reg
                            valuenode['type'] = spec[indexing_reg][f'rv{xlen}']['type']
                            error = check_values_in_type(indexing_reg, valuenode, spec, False)
                            if value_for_indexing_reg in index_val_list:
                                error.append(f'Founding repeating index-val {value_for_indexing_reg} for indexed csr : {csrname}')
                            else:
                                index_val_list.append(value_for_indexing_reg)
                            if error:
                                errors[csrname] = error

    return errors

def check_triggers(spec, logging):
    error = []
    xlen = 64 if 64 in spec['supported_xlen'] else 32
    indexed_registers = ['tdata1','tinfo','tdata1', 'tdata2', 'tcontrol', 'hcontext', 'scontext']
    ind_prop = {}

    for i in indexed_registers:
        ind_prop[i] = {}
        ind_prop[i]['accessible'] = spec[i][f'rv{xlen}']['accessible']
        if ind_prop[i]['accessible']:
            ind_prop[i]['size'] = len(spec[i][f'rv{xlen}']['index_list'])
            ind_prop[i]['index_vals'] = []
            for x in spec[i][f'rv{xlen}']['index_list']:
                ind_prop[i]['index_vals'].append(x['index_val'])
        else:
            ind_prop[i]['size'] = 0
            ind_prop[i]['index_vals'] = []


    for i in ind_prop:
        for j in ind_prop:
            if j != i and ind_prop[i]['accessible'] and \
                    ind_prop[j]['accessible']:
                if ind_prop[j]['size'] != ind_prop[i]['size']:
                    error.append(f"The size of indexed registers {i} and {j} do not match")
                if ind_prop[j]['index_vals'] != ind_prop[i]['index_vals']:
                    error.append(f"The index_vals of indexed registers {i} and {j} do not match")
    errors = {}
    if error:
        errors["TRIGGERS"] = error
    return errors

def check_debug_specs(debug_spec, isa_spec,
                work_dir,
                logging=False,
                no_anchors=False):
    '''
        Function to perform ensure that the isa and debug specifications confirm
        to their schemas. The :py:mod:`Cerberus` module is used to validate that the
        specifications confirm to their respective schemas.


        :param debug_spec: The path to the DUT debug specification yaml file.

        :param isa_spec: The path to the DUT isa specification yaml file.

        :param logging: A boolean to indicate whether log is to be printed.

        :type logging: bool

        :type isa_spec: str

        :raise ValidationError: It is raised when the specifications violate the
            schema rules. It also contains the specific errors in each of the fields.

        :return: A tuple with the first entry being the absolute path to normalized isa file
            and the second being the absolute path to the platform spec file.
    '''

    foo1 = isa_spec
    foo = debug_spec
    schema = constants.debug_schema
    """
      Read the input-isa foo (yaml file) and validate with schema-isa for feature values
      and constraints
    """
    # Load input YAML file
    if logging:
        logger.info('DebugCheck: Loading input Debug file: ' + str(foo))
    master_inp_debug_yaml = utils.load_yaml(foo, no_anchors)

    # Load input YAML file
    if logging:
        logger.info('DebugCheck: Loading input isa file for debug: ' + str(foo1))
    master_inp_yaml = utils.load_yaml(foo1, no_anchors)
    isa_string = master_inp_yaml['hart0']['ISA']

    # instantiate validator
    if logging:
        logger.info('DebugCheck: Load Debug Schema ' + str(schema))
    master_schema_yaml = utils.load_yaml(schema, no_anchors)

    outyaml = copy.deepcopy(master_inp_debug_yaml)
    for x in master_inp_debug_yaml['hart_ids']:
        if logging:
            logger.info(f'DebugCheck: Processing Hart:{x}')
        inp_debug_yaml = master_inp_debug_yaml['hart'+str(x)]
        schema_yaml = add_debug_setters(master_schema_yaml['hart_schema']['schema'])
        #Extract xlen
        xlen = inp_debug_yaml['supported_xlen']

        validator = schemaValidator(schema_yaml, xlen=xlen, isa_string=isa_string)
        validator.allow_unknown = False
        validator.purge_readonly = True
        normalized = validator.normalized(inp_debug_yaml, schema_yaml)

        # Perform Validation
        if logging:
            logger.info(f'DebugCheck: Initiating Validation for hart:{x}')
        valid = validator.validate(normalized)

        # Print out errors
        if valid:
            if logging:
                logger.info(f'DebugCheck: No errors for Hart:{x}')
        else:
            error_list = validator.errors
            raise ValidationError("Error in " + foo + ".", error_list)

        normalized['ISA'] = isa_string

        if logging:
            logger.info(f'DebugCheck: Updating fields node for each CSR in Hart:{x}')
        normalized = update_fields(normalized, logging)

        outyaml['hart'+str(x)] = trim(normalized)
    file_name = os.path.split(foo)
    file_name_split = file_name[1].split('.')
    output_filename = os.path.join(
        work_dir, file_name_split[0] + '_checked.' + file_name_split[1])
    dfile = output_filename
    outfile = open(output_filename, 'w')
    if logging:
        logger.info('DebugCheck: Dumping out Normalized Checked YAML: ' + output_filename)
    utils.dump_yaml(outyaml, outfile, no_anchors )
    return dfile

def check_isa_specs(isa_spec,
                work_dir,
                logging=False,
                no_anchors=False):
    '''
        Function to perform ensure that the isa and platform specifications confirm
        to their schemas. The :py:mod:`Cerberus` module is used to validate that the
        specifications confirm to their respective schemas.

        :param isa_spec: The path to the DUT isa specification yaml file.

        :param logging: A boolean to indicate whether log is to be printed.

        :type logging: bool

        :type isa_spec: str

        :raise ValidationError: It is raised when the specifications violate the
            schema rules. It also contains the specific errors in each of the fields.

        :return: A tuple with the first entry being the absolute path to normalized isa file
            and the second being the absolute path to the platform spec file.
    '''
    global inp_yaml

    if logging:
        logger.info('Input-ISA file')

    foo = isa_spec
    schema = constants.isa_schema
    """
      Read the input-isa foo (yaml file) and validate with schema-isa for feature values
      and constraints
    """
    # Load input YAML file
    if logging:
        logger.info('ISACheck: Loading input file: ' + str(foo))
    master_inp_yaml = utils.load_yaml(foo, no_anchors)

    # instantiate validator
    if logging:
        logger.info('ISACheck: Load Schema ' + str(schema))
    master_schema_yaml = utils.load_yaml(schema, no_anchors)

    outyaml = copy.deepcopy(master_inp_yaml)
    for x in master_inp_yaml['hart_ids']:
        if logging:
            logger.info(f'ISACheck: Processing Hart:{x}')
        inp_yaml = master_inp_yaml['hart'+str(x)]
        schema_yaml = add_def_setters(master_schema_yaml['hart_schema']['schema'])
        schema_yaml = add_reset_setters(master_schema_yaml['hart_schema']['schema'])
        schema_yaml = add_fflags_type_setters(master_schema_yaml['hart_schema']['schema'])
        #Extract xlen
        xlen = inp_yaml['supported_xlen']
        validator = schemaValidator(schema_yaml, xlen=xlen, isa_string=inp_yaml['ISA'])
        validator.allow_unknown = False
        validator.purge_readonly = True
        normalized = validator.normalized(inp_yaml, schema_yaml)

        # Perform Validation
        if logging:
            logger.info(f'ISACheck: Initiating Validation for Hart:{x}')
        valid = validator.validate(normalized)

        # Print out errors
        if valid:
            if logging:
                logger.info(f'ISACheck: No errors for Hart:{x}')
        else:
            error_list = validator.errors
            raise ValidationError(f"ISACheck: Error in " + foo + ".", error_list)
        if logging:
            logger.info(f'ISACheck:  Updating fields node for each CSR in Hart:{x}')
        normalized = update_fields(normalized, logging)

        outyaml['hart'+str(x)] = trim(normalized)
    file_name = os.path.split(foo)
    file_name_split = file_name[1].split('.')
    output_filename = os.path.join(
        work_dir, file_name_split[0] + '_checked.' + file_name_split[1])
    ifile = output_filename
    outfile = open(output_filename, 'w')
    if logging:
        logger.info('ISACheck: Dumping out Normalized Checked YAML: ' + output_filename)
    utils.dump_yaml(outyaml, outfile, no_anchors )
    return ifile

def check_custom_specs(custom_spec,
                work_dir,
                logging=False,
                no_anchors=False):
    '''
        Function to perform ensure that the isa and platform specifications confirm
        to their schemas. The :py:mod:`Cerberus` module is used to validate that the
        specifications confirm to their respective schemas.

        :param isa_spec: The path to the DUT isa specification yaml file.

        :param logging: A boolean to indicate whether log is to be printed.

        :type logging: bool

        :type isa_spec: str

        :raise ValidationError: It is raised when the specifications violate the
            schema rules. It also contains the specific errors in each of the fields.

        :return: A tuple with the first entry being the absolute path to normalized isa file
            and the second being the absolute path to the platform spec file.
    '''
    if logging:
        logger.info('Custom CSR Spec')

    foo = custom_spec

    # Load input YAML file
    if logging:
        logger.info('CustomCheck: Loading input file: ' + str(foo))
    master_custom_yaml = utils.load_yaml(foo, no_anchors)
    schema_yaml = utils.load_yaml(constants.custom_schema, no_anchors)
    validator = schemaValidator(schema_yaml, xlen=[])
    validator.allow_unknown = True

    outyaml = copy.deepcopy(master_custom_yaml)
    for x in master_custom_yaml['hart_ids']:
        if logging:
            logger.info(f'CustomCheck: Processing Hart:{x}')
        inp_yaml = master_custom_yaml['hart'+str(x)]
        valid = validator.validate(inp_yaml)
        if valid:
            if logging:
                logger.info(f'CustomCheck: No errors for Hart:{x}')
        else:
            error_list = validator.errors
            raise ValidationError("CustomCheck: Error in " + foo + ".", error_list)
        normalized = validator.normalized(inp_yaml, schema_yaml)
        if logging:
            logger.info(f'CustomCheck: Updating fields node for each CSR Hart:{x}')
        normalized = update_fields(normalized, logging)
        outyaml['hart'+str(x)] = trim(normalized)
    errors = check_fields(inp_yaml)
    if errors:
            raise ValidationError("Error in " + foo + ".", errors)
    outyaml['hart'+str(x)] = trim(inp_yaml)
    file_name = os.path.split(foo)
    file_name_split = file_name[1].split('.')
    output_filename = os.path.join(
        work_dir, file_name_split[0] + '_checked.' + file_name_split[1])
    cfile = output_filename
    outfile = open(output_filename, 'w')
    if logging:
        logger.info('CustomCheck: Dumping out Normalized Checked YAML: ' + output_filename)
    utils.dump_yaml(outyaml, outfile, no_anchors )
    return cfile

def check_platform_specs(platform_spec,
                work_dir,
                logging=False,
                no_anchors=False):
    foo = platform_spec
    schema = constants.platform_schema
    if logging:
        logger.info('Input-Platform file')
    """
      Read the input-platform foo (yaml file) and validate with schema-platform for feature values
      and constraints
    """
    # Load input YAML file
    if logging:
        logger.info('Loading input file: ' + str(foo))
    inp_yaml = utils.load_yaml(foo, no_anchors)
    if inp_yaml is None:
        inp_yaml = {'mtime': {'implemented': False}}

    # instantiate validator
    if logging:
        logger.info('Load Schema ' + str(schema))
    schema_yaml = utils.load_yaml(schema, no_anchors)
    validator = schemaValidator(schema_yaml, xlen=[])
    validator.allow_unknown = False
    validator.purge_readonly = True
    normalized = validator.normalized(inp_yaml, schema_yaml)

    # Perform Validation
    if logging:
        logger.info('Initiating Validation')
    valid = validator.validate(normalized)

    # Print out errors
    if valid:
        if logging:
            logger.info('No Syntax errors in Input Platform Yaml. :)')
    else:
        error_list = validator.errors
        raise ValidationError("Error in " + foo + ".", error_list)

    file_name = os.path.split(foo)
    file_name_split = file_name[1].split('.')
    output_filename = os.path.join(
        work_dir, file_name_split[0] + '_checked.' + file_name_split[1])
    pfile = output_filename
    outfile = open(output_filename, 'w')
    if logging:
        logger.info('Dumping out Normalized Checked YAML: ' + output_filename)
    utils.dump_yaml(trim(normalized), outfile, no_anchors)

    return pfile

def check_csr_specs(ispec=None, customspec=None, dspec=None, pspec=None, work_dir=None, logging=False, no_anchors=True) -> list:
    '''
        Merge the isa, custom and debug CSR specs into a single CSR spec file.
        Perform all warl checks on this merged CSR spec file.
        This function needs to be called hart-wise.

        :param ispec: The isa spec yaml. Defaults to None.
        :param customspec: The custom spec yaml. Defaults to None.
        :param dspec: The debug spec yaml. Defaults to None.
        :param pspec: The platform spec yaml. Defaults to None.
        :param work_dir: The working directory. Defaults to None.
        :param logging: A boolean to indicate whether log is to be printed. Defaults to False.
        :param no_anchors: A boolean to indicate whether anchors are not to be used. Defaults to True.

        :type ispec: dict
        :type customspec: dict
        :type dspec: dict
        :type pspec: dict
        :type work_dir: str
        :type logging: bool
        :type no_anchors: bool

        :return: List of validated CSR specs. Position holds 'None' if a certain spec was not passed.
    '''

    if ispec is not None:
        isa_file = check_isa_specs(os.path.abspath(ispec), work_dir, logging, no_anchors)
    else:
        logger.error("ISA spec not passed. This is mandatory.")
        isa_file = None
        raise SystemExit

    if customspec is not None:
        custom_file = check_custom_specs(os.path.abspath(customspec), work_dir, logging, no_anchors)
    else:
        custom_file = None

    if dspec is not None:
        debug_file = check_debug_specs(os.path.abspath(dspec), ispec, work_dir, logging, no_anchors)
    else:
        debug_file = None

    if pspec is not None:
        platform_file = check_platform_specs(os.path.abspath(pspec), work_dir, logging, no_anchors)
    else:
        platform_file = None

    specs_list = [isa_file, custom_file, debug_file, platform_file]

    if logging:
        logger.info("Initiating checks on all CSR specs.")

    # merge the dicts ispec, customspec and dspec after loading the YAMLs into dicts
    ispec_dict = utils.load_yaml(isa_file, no_anchors)
    customspec_dict = utils.load_yaml(custom_file, no_anchors) if custom_file is not None else {}
    dspec_dict = utils.load_yaml(debug_file, no_anchors) if debug_file is not None else {}

    merged = {}
    hart_ids = []
    for entry in ispec_dict['hart_ids']:
        hart_ids.append(entry)
        merged[f'hart{entry}'] = {}
        merged[f'hart{entry}'].update(ispec_dict['hart'+str(entry)])
        if custom_file is not None:
            merged[f'hart{entry}'].update(customspec_dict['hart'+str(entry)])
        if debug_file is not None:
            merged[f'hart{entry}'].update(dspec_dict['hart'+str(entry)])

        try:
            uarch_signals = merged[f'hart{entry}']['uarch_signals']
        except KeyError as e:
            logger.info(f"No uarch signals found for hart:{entry}")
            uarch_signals = {}
    
    for entry in hart_ids:
        csr_db = merged[f'hart{entry}']
        if logging:
            logger.info(f"Initiating WARL legality checks for hart:{entry}.")
        errors = check_warl_legality(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        errors = check_supervisor(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        if logging:
            logger.info(f"Initiating post processing and reset value checks for hart{entry}.")
        errors = check_reset(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        if csr_db['mhartid']['reset-val'] != entry:
            raise ValidationError('Error in csr definitions.',
                    {'mhartid': ['wrong reset-val of for hart'+str(entry)]})

        if logging:
            logger.info(f'Initiating validation checks for indexed csrs')
        errors = check_indexing(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        if logging:
            logger.info(f'Initiating validation checks for shadow fields')
        errors = check_shadows(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        errors = check_mhpm(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        errors = check_pmp(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        if logging:
            logger.info(f'Initiating validation checks for trigger csrs')
        if dspec_dict == {}:
            if logging:
                logger.warning(f'No debug spec passed. Skipping trigger checks.')
        else:
            errors = check_triggers(csr_db, logging)
        if errors:
            raise ValidationError("Error in csr definitions", errors)

        if logging and not errors:
            logger.info(f'All checks completed for hart{entry}. No errors found.')

    return specs_list
