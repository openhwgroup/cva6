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
""" Module is used to factorize multiples registers with the same name 
    to a specific format of registers """
import re


def address_to_key(address):
    return int(address, 16)


def factorizer(yaml_data):
    privname = None
    fieldname = []
    regname = []
    regdescr = []
    regadress = []
    reg_number = []
    new_regname = []
    data = []
    field_suffix = []
    suffix_name = []
    suffix_descr = []
    suffix_address = []
    suffix_number = []
    key_to_remove = []
    for key, value in yaml_data["hart0"].items():
        if isinstance(value, dict):
            regelement = yaml_data["hart0"].get(key, {})
            if regelement.get("address", None):
                regaddress = hex(regelement.get("address", None))
            else:
                regaddress = ""
            if regelement.get("description", ""):
                desc = regelement.get("description", "")
            else:
                desc = ""
            if regelement.get("rv32", "")["accessible"]:
                pattern = r"(\D+)(\d+)(.*)"
                match = re.search(pattern, key)
                if match:
                    key_to_remove.append(key)
                    if privname and match.group(1) == privname.group(1):
                        if len(match.group(3)) > 0:
                            suffix_name.append(match.group(0))
                            field_suffix.append(match.group(1))
                            suffix_number.append(match.group(2))
                            suffix_descr.append(desc)
                            suffix_address.append((regaddress))
                        else:
                            fieldname.append(match.group(1))
                            regname.append(match.group(0))
                            reg_number.append(match.group(2))
                            regdescr.append(desc)
                            regadress.append(regaddress)
                    else:
                        if regname:
                            regadress = sorted(regadress, key=address_to_key)
                            regname = sorted(
                                regname, key=lambda x: int(x.lstrip(fieldname[0]))
                            )
                            start_address = hex(int(regadress[0], 16))
                            desc = str(regdescr[0])
                            desc = re.sub(str(regname[0]), fieldname[0], desc)
                            modified_data = yaml_data["hart0"][regname[0]].copy()
                            modified_data["address"] = (
                                f"{str(start_address)}-{str(regadress[-1])}"
                            )
                            new_regname.append(
                                f"{fieldname[0]}[{reg_number[0]}-{reg_number[-1]}]"
                            )
                            data.append(modified_data)
                        regname = [match.group(0)]
                        fieldname = [match.group(1)]
                        reg_number = [match.group(2)]
                        regdescr = []
                        regadress = [regaddress]
                        if suffix_name:
                            suffix_name = sorted(
                                suffix_name,
                                key=lambda x: int(
                                    x.lstrip(field_suffix[0]).rstrip("h")
                                ),
                            )
                            suffix_address = sorted(suffix_address, key=address_to_key)
                            desc = str(suffix_descr[0])
                            desc = re.sub(str(suffix_name[0]), field_suffix[0], desc)
                            modified_data = yaml_data["hart0"][suffix_name[0]].copy()
                            modified_data["address"] = (
                                f"{str(suffix_address[0])}-{str(suffix_address[-1])}"
                            )
                            new_regname.append(
                                f"{field_suffix[0]}[{suffix_number[0]}-{suffix_number[-1]}]h"
                            )
                            data.append(modified_data)
                        suffix_name = []
                        field_suffix = []
                        regdescr = []
                        suffix_number = [match.group(2)]
                        suffix_address = []
                    privname = match
    if regname:
        start_address = hex(int(regadress[0], 16))
        end_address = str(regadress[-1])
        desc = str(regdescr[0])
        desc = re.sub(str(regname[0]), fieldname[0], desc)
        modified_data = yaml_data["hart0"][regname[0]].copy()
        modified_data["description"] = desc
        modified_data["address"] = f"{str(start_address)}-{str(end_address)}"
        new_regname.append(f"{fieldname[0]}[{reg_number[0]}-{reg_number[-1]}]")
        data.append(modified_data)
        regname = []
        regdescr = []
        regadress = []
        fieldname = []
    if suffix_name:
        desc = str(suffix_descr[0])
        desc = re.sub(str(suffix_name[0]), field_suffix[0], desc)
        modified_data = yaml_data["hart0"][suffix_name[0]].copy()
        modified_data["description"] = desc
        modified_data["address"] = (
            f"{str(hex(int(suffix_address[0],16)))}-{str(suffix_address[-1])}"
        )
        new_regname.append(
            f"{field_suffix[0]}[{suffix_number[0]}-{suffix_number[-1]}]h"
        )
        data.append(modified_data)
        suffix_name = []
        field_suffix = []
        regdescr = []
        regadress = []
    for index, reg in enumerate(new_regname):
        yaml_data["hart0"][reg] = data[index]
    for key in key_to_remove:
        del yaml_data["hart0"][key]
    return yaml_data["hart0"]
