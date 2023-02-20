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
from collections import OrderedDict
import re

# Load the configuration associated with the current platform
if "PLATFORM_TOP_DIR" in os.environ:
    lib_path = os.path.abspath(os.path.join(os.environ["PLATFORM_TOP_DIR"], "vptool"))
    sys.path.append(lib_path)
    try:
        import vp_config

        vp_config.io_fmt_gitrev = "$Id$"
    except Exception as e:
        print("ERROR: Please define path to vp_config package (got %s!)" % str(e))
        sys.exit(1)
else:
    print("ERROR: Environment variable 'PLATFORM_TOP_DIR' not set, cannot continue!")
    sys.exit(1)

# Remove non-ASCII characters from a string.
def remove_non_ascii(s):
    return "".join([x for x in s if ord(x) < 128])


# Normalize a heritage VP_IPnnn_Pnnn_Innn tag
# to VP_<PROJECT_NAME>_Fnnn_Snnn_Innn form.
def normalize_tag(l):
    pattern_oldstyle = re.compile(r"VP_IP([0-9]+)_P([0-9]+)_I([0-9]+)$")
    match = pattern_oldstyle.match(l)
    if match and match.group() == l:
        # Full match
        return "VP_" + vp_config.PROJECT_IDENT + "_F%s_S%s_I%s" % match.groups()
    else:
        # Partial match or no match at all: return unmodified label.
        return l


#####################################
##### Class Definition

class VerifItem:
    """
    A Verification Item captures a specific aspect of a design that
    can be individually verified.
    Verification Items are intended to be instantiated in a Subfeature
    class which groups Verification Items related to a given property of
    the design, e.g. to one instruction of an Instruction Set.
    """
    # Class variable: Names of Python attributes of a Verification Item that
    # can be free-form strings and have default cue strings defined.
    attr_names = [
        "description",
        "reqt_doc",  # Note the 'd' in '_doc'...
        "verif_goals",
        "coverage_loc",
        "comments"
    ]
    # Class variable: Matching names in Yaml-based GUI configuration
    gui_fields = [
        "feature_descr",
        "requirement_loc",
        "verif_goals",
        "coverage_loc",
        "comments",
    ]

    def __init__(self, name=0, tag="", description=""):
        # Identifier of the Item, used in display lists.
        self.name = name
        # Unique tag of the Verificataion Item (never to be reused).
        self.tag = tag
        # Description of the property to be verified.
        self.description = description
        # Document containing the corresponding requirement or design spec.
        self.reqt_doc = ""
        # Viewing information for the requirement/design document.
        self.ref_mode = "page"
        self.ref_page = ""
        self.ref_section = ""
        self.ref_viewer = "firefox"
        # Goals of verification
        self.verif_goals = ""
        # Pass/fail criteria
        self.pfc = -1       # None selected, must choose
        # Test type
        self.test_type = -1 # None selected, must choose
        # Coverage method
        self.cov_method = -1 # None selected, must choose
        # Applicable cores
        self.cores = -1  # By default, a new Verif Item is applicable to all cores.
        # Pointer to coverage data
        self.coverage_loc = ""
        # User comments for the verification item
        self.comments = ""

    def to_Item(self):
        """
        Convert a VerifItem to a legacy-style Item object.
        """
        result = Item(self.name, self.tag, self.description, self.reqt_doc)
        # These attributes are a 1-to-1 match.
        for attr in [
            "ref_mode", "ref_page", "ref_section", "ref_viewer", "verif_goals",
            "pfc", "test_type", "cov_method", "cores", "coverage_loc", "comments",
        ]:
            setattr(result, attr, getattr(self, attr))
        return result

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
        # Requirement to be verified (from now on, the design document...)
        # FIXME: field naming needs a major rework.
        self.purpose = purpose
        # Summary of verification goals
        self.verif_goals = ""
        # Location of coverage data
        self.coverage_loc = ""
        # Use page as the default reference mode for design docs.
        # This will work with all files (no reliance on named dests).
        self.ref_mode = "page"
        self.ref_page = ""
        self.ref_section = ""
        self.ref_viewer = "firefox"
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

    def to_VerifItem(self):
        """
        Convert an Item to a VerifItem.  Keep only the information that's needed.
        """
        result = VerifItem(self.name, self.tag, self.description)
        result.reqt_doc = self.purpose
        # These attributes may be missing on objects coming from older VPTOOL versions.
        for attr in ["ref_mode", "ref_page", "ref_section", "ref_viewer"]:
            if hasattr(self, attr):
                setattr(result, attr, getattr(self, attr))
            else:
                setattr(result, attr, "")
        # The following attributes were already mandatory in older RISC-V VPTOOL versions.
        for attr in [
            "verif_goals",
            "pfc", "test_type", "cov_method", "cores", "coverage_loc", "comments",
        ]:
            setattr(result, attr, getattr(self, attr))
        return result

    def attrval2str(self, attr):
        if attr == "cores" and "cores" in vp_config.yaml_config:
            # 'cores' are at toplevel of the Yaml config and the attr value is a bitmap.
            # Select entries corresponding to each bit that is set
            # and return a comma-separated list of associated names.
            matches = [
                x["label"]
                for x in vp_config.yaml_config[attr]["values"]
                if x["value"] & getattr(self, attr) != 0
            ]
            if len(matches) == 0:
                return "None applicable"
            else:
                return ", ".join(matches)
        elif "values" in vp_config.yaml_config["gui"][attr]:
            # This attribute takes predefined values.
            # A single value is allowed.
            if (
                getattr(self, attr)
                == vp_config.yaml_config["gui"][attr]["default"]["value"]
            ):
                return "NDY (Not Defined Yet)"
            else:
                matches = [
                    x["label"]
                    for x in vp_config.yaml_config["gui"][attr]["values"]
                    if x["value"] == getattr(self, attr)
                ]
                if len(matches) == 0:
                    return "<UNKNOWN>"
                else:
                    return matches[0]
        else:
            return "N/A (unsupported field '%s')" % attr

    def preserve_linebrs(self, text, indent="  "):
        """Preserve line breaks in the text by inserting two spaces before
        each newline.  Ensure first line of 'text' starts on a new line."""
        md_linebreak = "  \n" + indent
        return md_linebreak + md_linebreak.join(text.split("\n"))

    def __str__(self):
        return0 = ""
        return0 += format("#### Item: %s\n\n" % self.name)
        return0 += format("* **Requirement location:** %s\n" % self.purpose)
        return0 += format(
            "* **Feature Description**\n%s\n" % self.preserve_linebrs(self.description)
        )
        return0 += format(
            "* **Verification Goals**\n%s\n" % self.preserve_linebrs(self.verif_goals)
        )
        return0 += format("* **Pass/Fail Criteria:** %s\n" % self.attrval2str("pfc"))
        return0 += format("* **Test Type:** %s\n" % self.attrval2str("test_type"))
        return0 += format(
            "* **Coverage Method:** %s\n" % self.attrval2str("cov_method")
        )
        return0 += format("* **Applicable Cores:** %s\n" % self.attrval2str("cores"))
        return0 += format(
            "* **Unique verification tag:** %s\n" % normalize_tag(self.tag)
        )
        return0 += format("* **Link to Coverage:** %s\n" % self.coverage_loc)
        return0 += format(
            "* **Comments**\n%s\n"
            % self.preserve_linebrs(self.comments if self.comments else "*(none)*\n")
        )
        return return0

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
        Sanitize item before saving:
        - Remove default values of text fields
        - Normalize old-style (VP_IPnnn_Pnnn_Innn) tags to full form with
          project ident.
        """
        for (attr, field) in zip(Item.attr_names, Item.gui_fields):
            if getattr(self, attr) == vp_config.yaml_config["gui"][field]["cue_text"]:
                setattr(self, attr, "")
        self.tag = normalize_tag(self.tag)


class Subfeature:
    """
    A Subfeature is a subset of a major design feature that is characterized
    by a distinctive property.  Therefore, the verification items related to
    that property are closely related and are grouped together into a list
    associated with the Subfeature.
    """
    def __init__(self, name="", tag=""):
        # Name of the subfeature
        self.name = name
        # Tag of the subfeature: Must be unique across all subfeatures.
        self.tag = tag
        # Index of the next item to be added (MUST INCREASE ON EVERY ADDITION!)
        self.next_elt_id = 0
        # Display order of the Subfeature
        self.display_order = 0
        # List of Verification Items in this feature: an OrderedDict.
        self.items = OrderedDict()

    def __str__(self):
        return format("### Sub-feature: %s\n\n" % (self.name))

    def add_item(self, tag, description=""):  # adds a Verification Item to subfeature
        new_item = VerifItem(
            str(self.next_elt_id).zfill(3),
            tag=tag + "_I" + str(self.next_elt_id).zfill(3),
            description=description,
        )
        self.items[str(self.next_elt_id).zfill(3)] = new_item
        self.next_elt_id += 1
        # Return a ref to the newly created item.
        return new_item

    def del_item(self, index):  # remove a verification item from the subfeature
        del self.items[index]

    def get_item_names(self):
        return [item.name for item in self.items.values()]

    def to_Prop(self):
        """
        Convert a Subfeature into legacy-stype Prop object.
        """
        result = Prop(self.name, self.tag, self.display_order)
        result.item_count = self.next_elt_id
        result.rfu_list = [[elt[0], elt[1].to_Item()] for elt in self.items.items()]
        result.item_list = dict(result.rfu_list)
        return result

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

    def to_Subfeature(self):
        """
        Convert a legacy Prop to a Subfeature, transfer only the fields that are required.
        """
        result = Subfeature(self.name, self.tag)
        # 'next_elt_id' needs extra care as 'item_count' assumes a contiguous
        # numbering of Items in Prop and will be inconsistent if items are removed.
        # Computing the max of item IDs is not reliable either in case the last
        # item was removed.
        #print("### Prop.to_Subfeature(tag='%s'): item_count = %d" % (self.tag, self.item_count))
        result.next_elt_id = self.item_count
        result.display_order = self.wid_order
        translated_items = [[elt[0], elt[1].to_VerifItem()] for elt in (self.item_list if self.item_list else self.rfu_list)]
        result.items = OrderedDict(translated_items)
        return result

    def __str__(self):
        return format("### Sub-feature: %s\n\n" % (self.name))

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

class Feature:
    """
    A Feature is a major group of design properties, for example
    a class of instructions or an operation mode of an interface.
    """
    # Class variable: highest Feature ID seen so far.
    _feature_count = 0

    def __init__(self, name="", id=""):
        # Index of next subfeature to add (MUST ALWAYS GROW upon adding subfeatures!)
        self.next_elt_id = 0
        # Name of the Feature
        self.name = name
        # Numerical ID of the Feature: Use the highest known value PLUS ONE
        # unless explicitly given (e.g., when converting Ip objects).
        if id != "":
            self.id = int(id)
        else:
            self.id = self.__class__._feature_count
            self.__class__._feature_count += 1
        # Display order of the Feature
        self.display_order = self.id
        # List of subfeatures
        self.subfeatures = OrderedDict()
        self.vptool_gitrev = ''
        self.io_fmt_gitrev = ''
        self.config_gitrev = ''
        self.ymlcfg_gitrev = ''

    def __str__(self):
        return format("## Feature: %s\n\n" % (self.name))

    def add_subfeature(self, name, tag=""):
        """
        Add a subfeature of the current feature.
        """
        if name in self.subfeatures.keys():
            print("Subfeature '%s' already exists in Feature '%s'!" % (name, self.name))
            feedback = 0
        else:
            name = remove_non_ascii(name)
            subfeature_name = str(self.next_elt_id).zfill(3) + "_" + str(name)
            self.next_elt_id += 1
            self.subfeatures[name] = Subfeature(
                subfeature_name,
                tag="VP_"
                + vp_config.PROJECT_IDENT
                + "_F"
                + str(self.ip_num).zfill(3)
                + "_S"
                + str(self.prop_count).zfill(3),
            )
            feedback = self.subfeatures[subfeature_name].tag
            self._count += 1
        return (feedback, subfeature_name)

    def del_subfeature(self, name):
        del self.subfeatures[str(name)]

    def to_Ip(self):
        """
        Convert a Feature to a legacy-stype Ip.
        """
        # Map Feature.id to Ip.ip_num.
        #print("### Feature.to_Ip(name='%s', id='%d')" % (self.name, self.id))
        result = Ip(self.name, self.id)
        result.prop_count = self.next_elt_id
        result.wid_order = self.display_order
        result.rfu_list = [[elt[0], elt[1].to_Prop()] for elt in self.subfeatures.items()]
        result.prop_list = dict(result.rfu_list)
        for attr in ["vptool_gitrev", "io_fmt_gitrev", "config_gitrev", "ymlcfg_gitrev"]:
            setattr(result, attr, getattr(self, attr))
        return result

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
        if index != "":
            self.ip_num = index  ## Store number creation
        else:
            self.ip_num = self.__class__._ip_count
        #print("### Created Ip(name='%s', index='%d')" % (self.name, self.ip_num))
        self.__class__._ip_count += 1
        self.wid_order = self.ip_num
        # rfu for future dev
        self.rfu_dict = {}
        self.rfu_list = []
        self.rfu_list_0 = []
        self.rfu_list_1 = []
        self.vptool_gitrev = ''
        self.io_fmt_gitrev = ''
        self.config_gitrev = ''
        self.ymlcfg_gitrev = ''

    def to_Feature(self):
        """
        Convert an Ip to a Feature.
        """
        # Map Ip.ip_num to Feature.id.
        result = Feature(self.name, self.ip_num)
        # Next_elf_it needs extra care as it is derived from the length of the list
        # of Properties / Subfeatures.
        result.next_elt_id = self.prop_count
        result.display_order = self.wid_order
        translated_subfeatures = [[elt[0], elt[1].to_Subfeature()] for elt in (self.prop_list if self.prop_list else self.rfu_list)]
        result.subfeatures = OrderedDict(translated_subfeatures)
        for attr in ["vptool_gitrev", "io_fmt_gitrev", "config_gitrev", "ymlcfg_gitrev"]:
            setattr(result, attr, getattr(self, attr))
        return result

    def __str__(self):
        return format("## Feature: %s\n\n" % (self.name))

    def add_property(self, name, tag="", custom_num=""):  # adds an Prop instance to Ip
        if name in list(self.prop_list.keys()):
            print("Property already exists")
            feedback = 0
        else:
            name = remove_non_ascii(name)
            prop_name = custom_num + str(self.prop_count).zfill(3) + "_" + str(name)
            self.prop_list[prop_name] = Prop(
                prop_name,
                tag="VP_"
                + vp_config.PROJECT_IDENT
                + "_F"
                + str(self.ip_num).zfill(3)
                + "_S"
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
        Pickle doesn't provide reproducible output for dicts. When saved, they are converted to lists.
        """
        self.rfu_list = sorted(list(self.prop_list.items()), key=lambda key: key[0])
        self.prop_list = {}

    def post_load(self):
        """
        Trick used to ensure pickle output file stability
        When loading saved db, lists are converted back to initial dicts.
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
