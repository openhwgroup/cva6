import os
import re

root = os.path.abspath(os.path.dirname(__file__))

isa_schema = os.path.join(root, 'schemas/schema_isa.yaml')
debug_schema = os.path.join(root, 'schemas/schema_debug.yaml')
platform_schema = os.path.join(root, 'schemas/schema_platform.yaml')
custom_schema = os.path.join(root, 'schemas/schema_custom.yaml')
Zvl_extensions = [
        "Zvl32b", "Zvl64b", "Zvl128b", "Zvl256b", "Zve512b", "Zvl1024b"
]
Zvef_extensions = [
        "Zve32f", "Zve64f"
]
Zved_extensions = [
        "Zve64d"
]
Zve_extensions = [
        "Zve32x",  "Zve64x"
] + Zvef_extensions + Zved_extensions

Z_extensions = [
        "Zicbom", "Zicbop", "Zicboz", "Zicntr", "Zicsr", "Zicond", "Zicfilp", "Zicfiss", "Zifencei", "Zihintpause", "Zihpm", "Zimop",
        "Zmmul",
        "Zam", "Zabha", "Zacas",
        "Zca", "Zcb", "Zcf", "Zcd" , "Zcmp", "Zcmt", "Zcmop", 
        "Zfh", "Zfa",
        "Zfinx", "Zdinx", "Zhinx", "Zhinxmin",
        "Ztso",
        "Zba", "Zbb", "Zbc", "Zbe", "Zbf", "Zbkb", "Zbkc", "Zbkx", "Zbm", "Zbp", "Zbpbo", "Zbr", "Zbs", "Zbt",
        "Zk", "Zkn", "Zknd", "Zkne", "Zknh", "Zkr", "Zks", "Zksed", "Zksh", "Zkt",
        "Zpn", "Zpsf"
] + Zve_extensions + Zvl_extensions

S_extensions = ['Smrnmi','Smdbltrp', 'Ssdbltrp', 'Svnapot','Svadu', 'Sddbltrp', 'Sdext']

sub_extensions = Z_extensions + S_extensions

isa_regex = \
        re.compile("^RV(32|64|128)[IE][ACDFGHJLMNPQSTUV]*(("+'|'.join(sub_extensions)+")(_("+'|'.join(sub_extensions)+"))*){,1}(X[a-z0-9]*)*(_X[a-z0-9]*)*$")
