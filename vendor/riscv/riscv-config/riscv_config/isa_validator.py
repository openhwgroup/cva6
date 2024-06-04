import riscv_config.constants as constants
from collections import Counter
import re

def get_extension_list(isa):
    extension_list = []
    err = False
    err_list = []
    if not constants.isa_regex.match(isa):
        err = True
        err_list.append(f'Input ISA string : {isa} does not match accepted canonical ordering')
        return (extension_list, err, err_list)

    
    str_match = re.findall('(?P<stdisa>[^\d]*?)(?!_)*(?P<zext>Z.*?)*(?P<sext>S[a-z]*)*(?P<xext>X[a-z0-9]*)*(_|$)',isa)
    extension_list= []
    standard_isa = ''
    zext_list = []
    for match in str_match:
        stdisa, zext, sext, xext, ignore = match
        if stdisa != '':
            for e in stdisa:
                extension_list.append(e)
            standard_isa = stdisa
        if zext != '':
            extension_list.append(zext)
            zext_list.append(zext)
        if sext != '':
            extension_list.append(sext)
        if xext != '':
            extension_list.append(xext)
    # check for duplicates
    counts = Counter(extension_list)
    duplicate_list = list([item for item in counts if counts[item]>1])
    if duplicate_list:
        err = True
        err_list.append(f'Found duplicate extensions in ISA string: {duplicate_list}')
        return (extension_list, err, err_list)

    # check ordering of ISA
    canonical_ordering = 'IEMAFDQLCBJKTPVNSHU'
    order_index = {c: i for i, c in enumerate(canonical_ordering)}
    for i in range(len(standard_isa)-1):
        a1 = standard_isa[i]
        a2 = standard_isa[i+1]
    
        if order_index[a1] > order_index[a2]:
            err = True
            err_list.append( "Alphabet '" + a1 + "' should occur after '" + a2)

    # check canonical ordering within Zextensions
    for i in range(len(zext_list)-1):
        a1 = zext_list[i][1].upper()
        a2 = zext_list[i+1][1].upper()
        a3 = zext_list[i][2]
        a4 = zext_list[i+1][2]
        if order_index[a1] > order_index[a2]:
            err = True
            err_list.append( f"Z extension {zext_list[i]} must occur after {zext_list[i+1]}")
        elif a1 == a2 and a3 > a4:
            err = True
            err_list.append( f"Within the Z{a1.lower()} category extension {zext_list[i]} must occur after {zext_list[i+1]}")
    if 'B' not in extension_list and (set(['Zba', 'Zbb', 'Zbs']) & set(extension_list) == set(['Zba', 'Zbb', 'Zbs'])):
        # Insert 'B' at correct location: after any of its predecessors in canonical ordering.
        # At least 'I' or 'E' must be present by definition.
        B_preds = canonical_ordering[:canonical_ordering.find('B')]
        lastpred_B_idx = max([pos for pos, char in enumerate(standard_isa) if char in list(B_preds)])
        extension_list.insert(lastpred_B_idx + 1, 'B')
    if 'I' not in extension_list and 'E' not in extension_list:
        err_list.append( 'Either of I or E base extensions need to be present in the ISA string')
        err = True
    if 'F' in extension_list and not "Zicsr" in extension_list:
        err_list.append( "F cannot exist without Zicsr.")
        err = True
    if 'D' in extension_list and not 'F' in extension_list:
        err_list.append( "D cannot exist without F.")
        err = True
    if 'Q' in extension_list and not 'D' in extension_list:
        err_list.append( "Q cannot exist without D and F.")
        err = True
    if 'Zam' in extension_list and not 'A' in extension_list:
        err_list.append( "Zam cannot exist without A.")
        err = True
    if 'N' in extension_list and not 'U' in extension_list:
        err_list.append( "N cannot exist without U.")
        err = True
    if 'S' in extension_list and not 'U' in extension_list:
        err_list.append( "S cannot exist without U.")
        err = True
    if 'Zkn' in extension_list and ( set(['Zbkb', 'Zbkc', 'Zbkx', 'Zkne', 'Zknd', 'Zknh']) & set(extension_list)):
        err_list.append( "Zkn is a superset of Zbkb, Zbkc, Zbkx, Zkne, Zknd, Zknh. In presence of Zkn the subsets must be ignored in the ISA string.")
        err = True
    if 'Zks' in extension_list and ( set(['Zbkb', 'Zbkc', 'Zbkx', 'Zksed', 'Zksh']) & set(extension_list) ):
        err_list.append( "Zks is a superset of Zbkb, Zbkc, Zbkx, Zksed, Zksh. In presence of Zks the subsets must be ignored in the ISA string.")
        err = True
    if 'Zk' in extension_list and ( set(['Zbkb', 'Zbkc', 'Zbkx', 'Zkne', 'Zknd',
        'Zknh', 'Zkn','Zkr','Zkt']) & set(extension_list)):
        err_list.append( "Zk is a superset of Zbkb, Zbkc, Zbkx, Zkne, Zknd, Zknh, Zkn, Zkt, Zkr. In presence of Zk the subsets must be ignored in the ISA string.")
        err = True
    if 'Zfinx' in extension_list and not "Zicsr" in extension_list:
        err_list.append( "Zfinx cannot exist without Zicsr.")
        err = True
    if 'F' in extension_list and "Zfinx" in extension_list:
        err_list.append( "F and Zfinx cannot exist together")
        err = True
    if 'Zdinx' in extension_list and not 'Zfinx' in extension_list:
        err_list.append( "Zdinx cannot exist without Zfinx.")
        err = True
    if 'Zhinx' in extension_list and not 'Zfinx' in extension_list:
        err_list.append( "Zhinx cannot exist without Zfinx.")
        err = True
    if 'Zhinx' in extension_list and 'Zfh' in extension_list:
        err_list.append( "Zhinx and Zfh cannot exist together.")
        err = True
    if 'Zhinxmin' in extension_list and not 'Zfinx' in extension_list:
        err_list.append( "Zhinxmin cannot exist without Zfinx.")
        err = True
    if 'Zhinxmin' in extension_list and 'Zfh' in extension_list:
        err_list.append( "Zhinxmin and Zfh cannot exist together.")
        err = True
    if 'Zfa' in extension_list and not 'Zfh' in extension_list:
        err_list.append( "Zfa cannot exist without Zfh.")
    if 'Zbpbo' in extension_list :
        if not 'Zpn' in extension_list :
            err_list.append( "'Zpn' is required.")
            err = True
    if 'Zpn' in extension_list :
        if not 'Zbpbo' in extension_list :
            err_list.append( "'Zbpbo' is required.")
            err = True
        if '64' in isa and not 'Zpsf' in extension_list :
            err_list.append( "RV64 requires 'Zpsf'.")
            err = True
        if not ('M' in extension_list or 'Zmmul' in extension_list):
            err_list.append("baseline multiplication extension not found.")
    if 'Zpsf' in extension_list and not err :
        if not 'Zbpbo' in extension_list :
            err_list.append( "'Zbpbo' is required.")
            err = True
        if not 'Zpn' in extension_list :
            err_list.append( "'Zpn' is required.")
            err = True

    # Check V extensions
    if 'V' in extension_list and 'D' not in extension_list:
        err_list.append("V cannot exist without D and F.")
        err = True
    if len(set(['V'] + constants.Zve_extensions) & set(extension_list)) > 1:
        err_list.append(f"V and Zve* cannot exist together.")
        err = True
    if (set(constants.Zvl_extensions) & set(extension_list)) and not (
        set(['V'] + constants.Zve_extensions) & set(extension_list)
    ):
        err_list.append("Zvl* cannot exist without V or Zve*.")
        err = True
    if set(constants.Zvef_extensions) & set(extension_list) and (
            {"F", "Zfinx"} & set(extension_list)
    ):
        err_list.append("Zve*f cannot exist without F or Zfinx.")
        err = True
    if (set(constants.Zved_extensions) & set(extension_list)) and not (
            {"D", "Zdinx"} & set(extension_list)
    ):
        err_list.append("Zve64d cannot exist without D or Zdinx.")
        err = True

    return (extension_list, err, err_list)

def get_march_mabi (isa : str, opt_remove_custom_exts: bool = False):
    '''
    This function returns the corresponding march and mabi argument values
    for RISC-V GCC

    arguments:
        isa:    (string) this is the isa string in canonical order
    
    returns:
        march:      (string) this is the string to be passed to -march to gcc for a given isa
        mabi:       (string) this is the string to be passed to -mabi for given isa
        march_list: (list) gives march as a list of all extensions as elements
        None:       if ISA validation throws error
    '''

    # march generation

    march = 'rv32' if '32' in isa else 'rv64'
    march_list = []
    march_list.append(march)

    # get extension list
    (ext_list, err, err_list) = get_extension_list(isa)

    # if isa validation throws errors, return None
    if err:
        return None

    # extensions to be nullified
    null_ext = [
        # privilege modes
        'U',
        'S',

        # rnmi
        'Smrnmi',

        # debug mode
        'Sdext',

        # performance counter
        'Zicntr',
        'Zihpm',
        
        # unratified Zb* extensions
        'Zbe',
        'Zbf',
        'Zbm',
        'Zbr',
    ]

    # add Zbp and Zbt to null_ext if Zbpbo is present
    if 'Zbpbo' in ext_list:
        null_ext += ['Zbp', 'Zbt']

    # remove all custom extensions
    for ext in ext_list:
        if ext.startswith('X'):
            if opt_remove_custom_exts:
                ext_list.remove(ext)

    # construct march
    for ext in ext_list:
        if ext not in null_ext:
            march_list.append(ext.lower())
            # suffix multicharacter extensions with '_' 
            if len(ext) == 1:
                march += ext.lower()
            else:
                # suffix multiline extensions with '_' 
                march = march + '_' + ext.lower()

    # mabi generation
    mabi = 'ilp32'
    if 'E' in ext_list:
      mabi += 'e'
    if 'F' in ext_list and 'D' in ext_list:
        mabi += 'd'
    elif 'F' in ext_list:
        mabi += 'f'
    
    if 'rv64' in march:
        mabi = mabi.replace('ilp32', 'lp64')
 
    return (march, mabi, march_list)
