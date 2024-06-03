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
""" Module is used to update csr based on yaml file called  csr updater"""
import re
import yaml


def csr_recursive_update(original_dict, csr_update):
    """
    Gets the data of the RISC-V Config Yaml file and
    update the value of sub key in RISC-V Config Yaml file
    (ex: reset-val , shadow_type)
    :param original_dict : parsed data of RISC-V Config Yaml file
           csr_update : parsed data of  CSR updater
    :return: data of RISC-V Config Yaml file updated
    """
    for key, value in csr_update.items():
        if key in original_dict.keys():
            if isinstance(value, dict):
                csr_recursive_update(original_dict[key], value)
            elif isinstance(value, bool):
                if isinstance(original_dict[key], dict):
                    for k in original_dict[key]:
                        print(k)
                        if isinstance(original_dict[key][k], dict):
                 
                            for sub_key in original_dict[key][k]:
                                original_dict[key][k][sub_key] = value
                        else:
                            original_dict[key][k] = value
                else:
                    original_dict[key] = value
            else:
                original_dict[key] = value


def csr_formatter(srcfile, modifile):
    # Read original dictionary from YAML  Source file
    with open(srcfile, "r", encoding="utf-8") as file:
        original_dict = yaml.safe_load(file)
    updated_values = {}
    if modifile is not None:
        with open(modifile, "r", encoding="utf-8") as file:
            updated_values = yaml.safe_load(file)
    # Update original_dict with values from updated_values recursively
    csr_recursive_update(original_dict["hart0"], updated_values)

    # Identify and remove keys within the range specified for each register
    keys_to_remove = []
    for key, value in updated_values.items():
        if "range" in value:
            range_value = value["range"]
            pattern = rf"{key}(\d+)"
            for k in original_dict["hart0"].keys():
                match = re.search(pattern, str(k))
                if match:
                    index = int(match.group(1))
                    if index >= range_value:
                        keys_to_remove.append(k)
    # Remove excluded keys based on the condition
    exclude_data = updated_values.get("exclude")
    if exclude_data:
        exclude_key = exclude_data.get("key")
        sub_key = exclude_data.get("sub_key")
        cond = exclude_data.get("cond")

        def remove_keys_recursive(dictionary):
            keys_to_remove = []
            for k, v in dictionary.items():
                if isinstance(v, dict):
                    if sub_key:
                        if v.get(exclude_key, {}).get(sub_key) == cond:
                            keys_to_remove.append(k)
                    else:
                        if v.get(exclude_key) == cond:
                            keys_to_remove.append(k)
                    remove_keys_recursive(v)
            for k in keys_to_remove:
                dictionary.pop(k)

        remove_keys_recursive(original_dict["hart0"])
        remove_keys_recursive(original_dict["hart0"])
    # Remove keys from original_dict
    for k in keys_to_remove:
        original_dict["hart0"].pop(k, None)
    # Remove keys from original_dict
    for k in keys_to_remove:
        original_dict.pop(k, None)
    return original_dict
