#############################################################################
# Copyright (C) 2022 Thales DIS France SAS
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
#
# Original Author: Zbigniew Chamski (zbigniew.chamski@thalesgroup.com)
#############################################################################
## Config is Project dependent. It is imported from platform_package
## PYTHON_PATH env variable could be used

import sys, os
from datetime import datetime

# Load the configuration associated with the current platform
if "PLATFORM_TOP_DIR" in os.environ:
    lib_path = os.path.abspath(os.path.join(os.environ["PLATFORM_TOP_DIR"], 'vptool'))
    sys.path.append(lib_path)
    try:
        import vp_config
    except Exception as e:
        print("ERROR: Please define path to vp_config package (got %s!)" % str(e))
        sys.exit(1)
else:
    print("ERROR: Environment variable 'PLATFORM_TOP_DIR' not set, cannot continue!")
    sys.exit(1)

# Remove non-ASCII characters from a string.
def remove_non_ascii(s):
    return "".join([x for x in s if ord(x) < 128])


#####################################
##### Class Definition
class Item:
    """
    An item defines a specific case to test depending on its parent property
    It is intended to be instantiated in Prop class
    """

    count = 0
    attr_names = ["description", "purpose", "verif_goals", "coverage_loc", "comments"]
    gui_fields = [
        "feature_descr",
        "requirement_loc",
        "verif_goals",
        "coverage_loc",
        "comments",
    ]

    def __init__(self, item_ref_name=0, tag="", description="", purpose=""):
        self.name = str(item_ref_name)
        self.tag = tag
        # Description of feature to be tested
        self.description = description
        # Requirement to be verified
        self.purpose = purpose
        # Summary of verification goals
        self.verif_goals = ""
        # Location of coverage data
        self.coverage_loc = ""
        # FIXME: Propagate default value from YAML config.
        self.pfc = -1  # none selected, must choose
        self.test_type = -1  # none selected, must choose
        self.cov_method = -1  # none selected, must choose
        self.cores = -1  # applicable to all cores
        self.comments = ""
        self.status = ""
        self.simu_target_list = []
        self.__class__.count += 1
        self.rfu_list = []
        self.rfu_list_2 = []
        self.rfu_dict = {}  # used as lock. will be updated with class update
        self.rfu_dict["lock_status"] = 0

    def __del__(self):
        self.__class__.count -= 1

    def invert_lock(self):
        if self.is_locked():
            self.rfu_dict["lock_status"] = 0
        else:
            self.rfu_dict["lock_status"] = " ".join(
                (str(datetime.now()), os.getlogin())
            )

    def unlock(self):
        self.rfu_dict["lock_status"] = 0

    def lock(self):
        self.rfu_dict["lock_status"] = " ".join((str(datetime.now()), os.getlogin()))

    def is_locked(self):
        return bool(self.rfu_dict["lock_status"])

    def get_lock_status(self):
        return str(self.rfu_dict["lock_status"])

    def prep_to_save(self):
        """
        Sanitize item before saving: Remove default values of text fields.
        """
        pass
        for (attr, field) in zip(Item.attr_names, Item.gui_fields):
            if getattr(self, attr) == vp_config.yaml_config["gui"][field]["cue_text"]:
                setattr(self, attr, "")


class Prop:
    """
    A Property defines a specific behaviour or an IP section, to be tested/verified
    It is intended to be instantiated in Ip class.
    It contains a collection of Items.
    """

    def __init__(self, name="", tag="", wid_order=0):
        self.item_count = (
            0  # determine how many items have been created for a given property
        )
        self.name = name
        self.tag = tag
        self.item_list = {}
        self.wid_order = wid_order
        ## rfu for future dev
        self.rfu_list = []
        self.rfu_list_1 = []
        self.rfu_list_2 = []
        self.rfu_dict = {}

    def prop_clone(self):
        new_prop = Prop()
        new_prop.item_count = self.item_count
        new_prop.name = self.name
        new_prop.tag = self.tag
        new_prop.item_list = self.item_list.copy()
        new_prop.wid_order = self.wid_order
        new_prop.rfu_list = self.rfu_list[:]
        new_prop.rfu_list_1 = self.rfu_list_1[:]
        new_prop.rfu_list_2 = self.rfu_list_2[:]
        new_prop.rfu_dict = self.rfu_dict.copy()
        return new_prop

    def add_item(self, tag, description="", purpose=""):  # adds an item to Prop
        new_item = Item(
            str(self.item_count).zfill(3),
            tag=tag + "_I" + str(self.item_count).zfill(3),
            description=description,
            purpose=purpose,
        )
        self.item_list[str(self.item_count).zfill(3)] = new_item
        self.item_count += 1
        # Return a ref to the newly created item.
        return new_item

    def del_item(self, index):  # remove an item from Prop
        if (
            index == max(self.item_list.keys()) and False
        ):  # Spare numbering option disabled by False statement.
            self.item_count -= 1  # if the element removed is the last one, one can decrement item_count to spare numbering
        del self.item_list[index]

    def get_item_name(self):
        item_list_name = []
        for item in self.item_list:
            item_list_name.append(item.name)
        return item_list_name

    def prep_to_save(self):
        """
        Trick used to ensure pickle output file stability
        Pickle doesn't provide reproductible output for dict. When saved, they are converted to list
        """
        # Sanitize items of this Prop.
        for item in self.item_list.values():
            item.prep_to_save()
        self.rfu_list = sorted(list(self.item_list.items()), key=lambda key: key[0])
        self.item_list = {}

    def post_load(self):
        """
        Trick used to ensure pickle output file stability
        When loading saved db, list are converted back to initial dict
        """
        for item_key, item_elt in self.rfu_list:
            self.item_list[item_key] = item_elt
        self.rfu_list = []

    def insert_item(self, item_name):
        """This is intended to be used in specific cases as it
        can changes every item numbering; Should not be used ater item is implemented in simulations
        It insert last item in self.item_list at insert index, and update item tag and name accordingly
        """
        insert_index = int(item_name) + 1
        updated_dict = {}
        insert_index_string = str(insert_index).zfill(3)
        to_insert = self.item_list.pop(max(self.item_list.keys()))
        for elt in list(self.item_list.keys()):
            if int(elt) < insert_index:
                updated_dict[elt] = self.item_list[elt]
            else:
                updated_dict[str(int(elt) + 1).zfill(3)] = self.item_list[elt]
                updated_dict[str(int(elt) + 1).zfill(3)].tag = updated_dict[
                    str(int(elt) + 1).zfill(3)
                ].tag[:-3] + str(int(elt) + 1).zfill(3)
                updated_dict[str(int(elt) + 1).zfill(3)].name = str(int(elt) + 1).zfill(
                    3
                )
        updated_dict[insert_index_string] = to_insert
        updated_dict[insert_index_string].tag = (
            updated_dict[insert_index_string].tag[:-3] + insert_index_string
        )
        updated_dict[insert_index_string].name = insert_index_string
        self.item_list = updated_dict

    def unlock_items(self):
        for item in list(self.item_list.values()):
            item.unlock()

    def lock_items(self):
        for item in list(self.item_list.values()):
            item.lock()


class Ip:
    """
    An IP defines a bloc instantiated at chip top level, or more generally, a design specification chapter
    needing to be covered by a verification plan.
    It contains a collection of Prop.
    """

    _ip_count = 0

    def __init__(self, name="", index=""):
        self.prop_count = 0  # determine how many prop have been created for a given IP
        self.name = name
        self.prop_list = {}
        if index:
            self.ip_num = index  ## Store number creation
        else:
            self.ip_num = self.__class__._ip_count
        self.__class__._ip_count += 1
        self.wid_order = self.ip_num
        # rfu for future dev
        self.rfu_dict = {}
        self.rfu_list = []
        self.rfu_list_0 = []
        self.rfu_list_1 = []

    def add_property(self, name, tag="", custom_num=""):  # adds an Prop instance to Ip
        if name in list(self.prop_list.keys()):
            print("Property already exists")
            feedback = 0
        else:
            name = remove_non_ascii(name)
            prop_name = custom_num + str(self.prop_count).zfill(3) + "_" + str(name)
            self.prop_list[prop_name] = Prop(
                prop_name,
                tag="VP_IP"
                + str(self.ip_num).zfill(3)
                + "_P"
                + str(self.prop_count).zfill(3),
                wid_order=self.prop_count,
            )
            feedback = self.prop_list[prop_name].tag
            self.prop_count += 1
        return (feedback, prop_name)

    def del_property(self, name):  # remove a Prop instance from Ip
        if (
            self.prop_count == int(self.prop_list[name].tag[-3:]) + 1
        ):  # with custom numbering max elt is not always the last one created
            self.prop_count -= 1
        del self.prop_list[str(name)]

    def clear(self):
        self.__class__._ip_count = 0

    def unlock_properties(self):
        """
        Unlock all Prop/Items of the IP
        """
        for prop in list(self.prop_list.values()):
            prop.unlock_items()

    def lock_properties(self):
        """
        Lock all Prop/Items of the IP
        """
        for prop in list(self.prop_list.values()):
            prop.lock_items()

    def unlock_ip(self):
        """
        Unlock all Prop/Items of the IP.
        """
        self.unlock_properties()

    def prep_to_save(self):
        """
        Trick used to ensure pickle output file stability
        Pickle doesn't provide reproductible output for dict. When saved, they are converted to list
        """
        self.rfu_list = sorted(list(self.prop_list.items()), key=lambda key: key[0])
        self.prop_list = {}

    def post_load(self):
        """
        Trick used to ensure pickle output file stability
        When loading saved db, list are converted back to initial dict
        """
        for prop_key, prop_elt in self.rfu_list:
            self.prop_list[prop_key] = prop_elt
        self.rfu_list = []

    def create_ip_tag_dict(self):
        ip_tag_dict = {}
        for prop in list(self.prop_list.values()):
            for item in list(prop.item_list.values()):
                ip_tag_dict[item.tag] = item
        return ip_tag_dict
