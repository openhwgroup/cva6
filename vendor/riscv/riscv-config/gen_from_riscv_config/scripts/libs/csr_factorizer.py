# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Original Author: Oukalrazqou Abdessamii

import re 
import yaml

def address_to_key(address):
	return int(address,16) 
def Factorizer(yaml_data):
    privname = None
    fieldname=[]
    regname =[]
    regdescr =[]
    regAdress =[]
    reg_number =[] 
    new_regname = []
    data =[]
    field_suffix = []
    suffix_name  = []
    suffix_descr = []
    suffix_address =[]
    suffix_number = []
    key_to_remove =[]
    for  key , value in yaml_data['hart0'].items():
       if isinstance(value ,  dict) :   
         RegElement = yaml_data['hart0'].get(key, {})
         regName = key
         regAddress = hex(RegElement.get("address", None)) if RegElement.get("address", None) is not None else None
         reset = hex(RegElement.get('reset-val', ''))
         size = int(yaml_data['hart0'].get('supported_xlen', '')[0] )
         access = RegElement.get('priv_mode', '')
         if  RegElement.get("description", '') != None:
                 desc = RegElement.get("description", '')
         else:
                   desc = ""
         RV32 =   RegElement.get('rv32','')['accessible']
         RV64 =   RegElement.get('rv64','')['accessible']
         if RegElement.get('rv32','')['accessible']:
               fields = RegElement.get('rv32','').get('fields', [])
         else :
               fields = []
         if RegElement.get('rv32','')['accessible']:
           pattern = r"(\D+)(\d+)(.*)"
           match  = re.search(pattern, key)
           if match :
            key_to_remove.append(key) 
            if privname and match.group(1) == privname.group(1) :
               if len(match.group(3))>0:
                suffix_name.append(match.group(0))
                field_suffix.append(match.group(1))
                suffix_number.append(match.group(2))
                suffix_descr.append(desc)
                suffix_address.append((regAddress))
               else :
                fieldname.append(match.group(1))
                regname.append(match.group(0))
                reg_number.append(match.group(2))
                regdescr.append(desc)
                regAdress.append(regAddress) 
          
            else:
                if regname:
                   regAdress = sorted(regAdress , key = address_to_key)
                   regname = sorted(regname , key = lambda x:int(x.lstrip(fieldname[0])))
                   start_address = hex(int(regAdress[0],16))
                   end_address = str(regAdress[-1])
                   Address = "{}-{}".format(str(start_address) ,str(regAdress[-1]))
                   desc =  str(regdescr[0]) 
                   #print(str(regdescr[0]))
                   desc = re.sub(str(regname[0]),fieldname[0] ,desc)
                   modified_data = yaml_data['hart0'][regname[0]].copy()
  
                   #modified_data['description'] = desc
                   modified_data['address'] = Address
                   Name = Name = "{}[{}-{}]".format(fieldname[0],reg_number[0],reg_number[-1])
                   new_regname.append(Name)
                   #fields.append("{}i".format(fieldname[0]))
                   data.append(modified_data)
                regname = [match.group(0)]
                fieldname = [match.group(1)]
                reg_number =[match.group(2)]
                regdescr= []
                regAdress=[regAddress]
                 
                    
                if suffix_name:
                   suffix_name = sorted(suffix_name , key = lambda x:int(x.lstrip(field_suffix[0]).rstrip('h')))
                   suffix_address= sorted(suffix_address , key = address_to_key)
                   Address = "{}-{}".format(str(suffix_address[0]),str(suffix_address[-1]))
                   desc =  str(suffix_descr[0])
                   desc = re.sub(str(suffix_name[0]),field_suffix[0] ,desc) 
                   modified_data = yaml_data['hart0'][suffix_name[0]].copy()
                   #modified_data['description'] = desc
                   modified_data['address'] = Address
                   fields = modified_data.get('rv32','').get('fields', [])
                   #fields.append("{}i".format(field_suffix[0]))
                   Name = "{}[{}-{}]h".format(field_suffix[0],suffix_number[0],suffix_number[-1])
                   new_regname.append(Name)
                   data.append(modified_data)
                suffix_name = []
                field_suffix =[]
                regdescr= []
                suffix_number = [match.group(2)]
                suffix_address=[]
            privname = match 
    if regname:
        start_address = hex(int(regAdress[0],16))
        end_address = str(regAdress[-1])
        Address = "{}-{}".format(str(start_address) ,str(end_address))
        desc =  str(regdescr[0])
        desc = re.sub(str(regname[0]),fieldname[0] ,desc) 
        modified_data = yaml_data['hart0'][regname[0]].copy()
        modified_data['description'] = desc
        modified_data['address'] = Address
        Name = "{}[{}-{}]".format(fieldname[0],reg_number[0],reg_number[-1])
        new_regname.append(Name)
        data.append(modified_data)
        regname = []
        regdescr= []
        regAdress=[]
        fieldname =[]
    if suffix_name:
        Address = "{}-{}".format(str(hex(int(suffix_address[0],16))),str(suffix_address[-1]))
        desc =  str(suffix_descr[0]) 
        desc = re.sub(str(suffix_name[0]),field_suffix[0] ,desc)
        modified_data = yaml_data['hart0'][suffix_name[0]].copy()
        modified_data['description'] = desc
        modified_data['address'] = Address
        Name = "{}[{}-{}]h".format(field_suffix[0],suffix_number[0],suffix_number[-1])
        new_regname.append(Name)
        data.append(modified_data)
        suffix_name = []
        field_suffix =[]
        regdescr= []
        regAdress=[]
    for Index in range(len(new_regname)):
       yaml_data['hart0'][new_regname[Index]] = data[Index]

    for key in key_to_remove :
       del yaml_data['hart0'][key]
    
    return yaml_data['hart0']
'''
with open('cs.yaml', 'w' ) as file : 
	 yaml.dump(yaml_data, file,sort_keys = False)
'''        

              
