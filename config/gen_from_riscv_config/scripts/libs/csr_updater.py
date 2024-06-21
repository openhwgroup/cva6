import re
import yaml


def csr_recursive_update(original_dict, csr_update):
    """
    Gets the data of the RISC-V Config Yaml file and
    updates the value of sub key in the RISC-V Config Yaml file
    (ex: reset-val, shadow_type)
    :param original_dict: parsed data of the RISC-V Config Yaml file
    :param csr_update: parsed data of the CSR updater
    :return: data of RISC-V Config Yaml file updated
    """
    for key, value in csr_update.items():
        if key in original_dict:
            if isinstance(value, dict) and isinstance(original_dict[key], dict):
                # If both are dicts, recurse
                if key == "type":
                    # Replace the entire type dictionary
                    original_dict[key] = value
                else:
                    csr_recursive_update(original_dict[key], value)
            else:
                # Replace the original value with the update value
                original_dict[key] = value


def csr_formatter(srcfile, customfile, modifile):
    # Read original dictionary from YAML source file
    with open(srcfile, "r", encoding="utf-8") as file:
        original_dict = yaml.safe_load(file)
    with open(customfile, "r", encoding="utf-8") as file:
        custom_dict = yaml.safe_load(file)
    
    isa_data = original_dict.copy()
    isa_data['hart0'].update(custom_dict["hart0"])
    updated_values = {}
    if modifile is not None:
        with open(modifile, "r", encoding="utf-8") as file:
            updated_values = yaml.safe_load(file)

    # Update original_dict with values from updated_values recursively
    csr_recursive_update(isa_data["hart0"], updated_values)

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

        remove_keys_recursive(isa_data["hart0"])
        remove_keys_recursive(isa_data["hart0"])
    # Remove keys from original_dict
    for k in keys_to_remove:
        isa_data["hart0"].pop(k, None)
    # Remove keys from original_dict
    for k in keys_to_remove:
        isa_data.pop(k, None)
    return isa_data
