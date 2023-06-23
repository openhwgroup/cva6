#!/usr/bin/python
# -*- coding: utf-8 -*-
#############################################################################
# Copyright (C) 2022 Thales DIS France SAS
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
#
# Original Author: Zbigniew Chamski (zbigniew.chamski@thalesgroup.com)
#############################################################################

import tkinter as tk
from ttkthemes import themed_tk
import tkinter.ttk as ttk
import tkinter.simpledialog
import tkinter.messagebox
from tkinter.filedialog import askopenfilename
from tkinter.filedialog import asksaveasfilename
import tkinter.colorchooser
from inspect import ismethod
import pickle
from collections import OrderedDict

# Use Ruamel YAML support
from ruamel.yaml import YAML, yaml_object
global db_yaml_engine
db_yaml_engine = YAML(typ='rt')

# import cPickle as pickle
# Configuration (env + Python + Yaml) is imported indirectly via vp_pack.
from vp_pack import *

db_yaml_engine.register_class(VerifItem)
db_yaml_engine.register_class(Subfeature)
db_yaml_engine.register_class(Feature)

import os, sys, pwd, glob, subprocess
from optparse import OptionParser, Option
from PIL import Image, ImageTk
import shutil
import hashlib

global ip_list  # Dict Containing IPs->Prop->item. Eventually, it contains the whole DB
global MASTER_LABEL_COLOR, SECONDARY_LABEL_COLOR, TERTIARY_LABEL_COLOR, BG_COLOR, LOCK_COLOR
global CUSTOM_NUM
global DEFAULT_CURSOR, SPECIAL_CURSOR

# OHG blue: #002d62
# OHG green: #20aa4d
MASTER_LABEL_COLOR = "#20aa4d"
SECONDARY_LABEL_COLOR = "#002d62"
TERTIARY_LABEL_COLOR = "DarkGreen"
BG_COLOR = "#f5f5f5"
LOCK_COLOR = "orange"
LOCK_EN_COLOR = "ForestGreen"
CUETEXT_COLOR = "grey60"
CUSTOM_NUM = ""  ## Defined if a custom num is needed to be inserted before Property name (ex: regroup a section)
PERSO_FILE = ".vp.pref"
YAML_CONFIG_FILE = "vptool.yml"
EDITOR = 1  ## Editor used to open external files
EDITOR_LIST = {1: "nedit", 2: "geany", 3: "gvim", 4: "gedit"}
#####################################
#### Locked IP dict
LOCKED_IP_DICT = {}
#####################################
#### Cursor type
DEFAULT_CURSOR = "arrow"
SPECIAL_CURSOR = "plus"
#####################################
##### GUI Functions


class MyText(tk.Text):
    """MyText derived from Text with additional features:
    Ctrl+a, ctrl, leftshift and arrow do not trigger <KEYPRESS binding>
    """

    def __init__(self, master, cue_text="", **kwargs):
        tk.Text.__init__(self, master, **kwargs)
        self.cue_text = cue_text
        self.bind("<Control-Key-a>", self.select_all)
        ## dummy binding to get specific commands out of <KEYPRESS> binding
        self.bind("<Control-Key-c>", lambda event: "")
        self.bind("<Control-Key-s>", lambda event: "")
        self.bind("<Control-Key-q>", lambda event: "")
        self.bind("<Shift_L>", lambda event: "")
        self.bind("<Left>", lambda event: "")
        self.bind("<Right>", lambda event: "")
        self.bind("<Up>", lambda event: "")
        self.bind("<Down>", lambda event: "")
        self.bind("<1>", lambda event: self.focus_set())

    def select_all(self, *args):
        self.focus_set()
        self.tag_add("sel", "1.0", "end")
        return "break"


class MyListWidget(ttk.LabelFrame):
    """
    This Widget is composed of a Listbox and Action Buttons
    """

    def __init__(
        self,
        master=None,
        MasterClass=None,
        reflist=[],
        text="",
        expand="yes",
        side=None,
        padx=1,
        pady=2,
        bdelfunc=None,
        baddfunc=None,
        width=20,
        height=4,
        spinfunc=None,
        spin_value=None,
        spin_vip_value=None,
        bdel_default="normal",
        style=None,
    ):
        ttk.LabelFrame.__init__(self, master, text=text, style=style)
        self._inlist = reflist
        self.lframe = ttk.Frame(self)
        self.bframe = ttk.Frame(self)
        self.wlist = tk.Listbox(
            self.lframe, exportselection=0, width=width, height=height, bg=BG_COLOR
        )
        self.sbar = ttk.Scrollbar(self.lframe)
        self.badd = ttk.Button(
            self.bframe, text="New", command=self.badd_action, state="disabled"
        )
        self.bdel = ttk.Button(
            self.bframe, text="Del", command=self.bdel_action, state="disabled"
        )
        self.baddfunc = baddfunc
        self.bdelfunc = bdelfunc
        self.bdel_default = bdel_default
        ## spinbox section
        self.spin_value = spin_value
        # self.spinfunc = spinfunc
        # self.spin = ttk.Spinbox(self,values=spin_value)
        # Set the default value of the Spinbox to the first value in list if available.
        # if self.spin_value and isinstance(self.spin_value, tuple) and len(self.spin_value) > 0:
        #   self.spin.set(self.spin_value[0])
        # self.spin.icursor(0)
        # self.spin.configure(state='readonly',command=self.spin_action)
        # self.spin.bind('<ButtonRelease-1>',self.spin_action)
        ## Vip spinbox
        self.spin_vip_value = spin_vip_value
        # self.spin_vip = ttk.Spinbox(self,values=spin_vip_value)
        # if self.spin_vip_value and isinstance(self.spin_vip_value, tuple) and len(self.spin_vip_value) > 0:
        #   self.spin_vip.set(self.spin_vip_value[0])
        # self.spin_vip.icursor(0)
        # self.spin_vip.configure(state='readonly',command=self.spin_action)
        ## config & pack
        self.lframe.pack()
        self.bframe.pack()
        self.wlist.pack()
        self.sbar.pack()
        self.badd.pack()
        self.bdel.pack()
        self._gconfigure(self._inlist)
        self.pack(side, expand, padx, pady)
        ## start reorder list section
        self.enable_reordering = 0
        self.wlist.bind("<Control-Button-3>", self.setCurrent)
        self.wlist.bind("<Control-ButtonRelease-3>", self.shiftSelection)
        self.curIndex = None
        self.selection_to_shift = []
        self.need_to_reorder = 0
        self.MasterClass = MasterClass

    def setCurrent(self, event):
        self.curIndex = self.wlist.nearest(event.y)
        self.selection_to_shift = self.get_multiple_selection()

    def shiftSelection(self, event):
        if self.enable_reordering:
            i = self.wlist.nearest(event.y)
            lst_to_move = []
            if i not in self.selection_to_shift:
                for index in reversed(self.selection_to_shift):
                    lst_to_move.append(self._inlist.pop(index))
                for elt in lst_to_move:
                    if i < self.curIndex:
                        self._inlist.insert(i, elt)
                    else:
                        self._inlist.insert(i - len(lst_to_move) + 1, elt)
            self.update_list(self._inlist)
            self.need_to_reorder = 1
            self.MasterClass.export_new_order(self._inlist)
            ## end reorder list section

    def __del__(self):
        """prefer destroy() inherited function to kill this widget, __del__ func is not reliable"""
        print("destroy")
        self.destroy()
        ttk.LabelFrame.__del__(self)

    def get_selection(self):
        if self.wlist.curselection():
            return self.wlist.get(int(self.wlist.curselection()[0]))

    def get_multiple_selection(self, index=1):
        mult_selection_list = []
        for elt in self.wlist.curselection():
            if index:
                mult_selection_list.append(int(elt))
            else:
                mult_selection_list.append(self.wlist.get(int(elt)))
        return mult_selection_list

    def _gconfigure(self, reflist):
        self.sbar.config(command=self.wlist.yview)
        self.wlist.config(yscrollcommand=self.sbar.set, bd=2)
        for index in range(len(reflist)):
            self.wlist.insert(index, reflist[index])

    def gcolor(self, color_dict):
        # ZC FIXME TODO: The handling of the selection fg/bg colors appears to be incorrect.
        current_selection = self.get_selection()
        for index, ip_name in enumerate(self._inlist):
            if ip_name in color_dict:
                if color_dict[ip_name] == pwd.getpwuid(os.getuid()).pw_name:
                    self.wlist.itemconfig(index, {"fg": LOCK_EN_COLOR})
                    if current_selection == ip_name:
                        self.wlist.config(selectforeground=LOCK_EN_COLOR)
                else:
                    self.wlist.itemconfig(index, {"bg": LOCK_COLOR})
                    if current_selection == ip_name:
                        self.wlist.config(selectforeground="darkred")
            else:
                self.wlist.itemconfig(index, {"bg": BG_COLOR})
                if current_selection == ip_name:
                    self.wlist.config(selectforeground="black")

    def pack(self, side, expand, padx, pady):
        self.sbar.pack(side="right", fill="y")
        self.wlist.pack(side="left", expand="yes", fill="both")
        self.bdel.pack(side="bottom", anchor="s", fill="x")
        self.badd.pack(side="bottom", anchor="s", fill="x")
        self.lframe.pack(side="top", expand="yes", fill="both")
        self.bframe.pack(side="bottom", fill="x")
        if self.spin_value:
            self.spin.pack(fill="x")
        if self.spin_vip_value:
            self.spin_vip.pack(fill="x")
        ttk.LabelFrame.pack(
            self, expand=expand, fill="both", side=side, padx=padx, pady=pady
        )

    def badd_action(self):
        if ismethod(self.baddfunc):
            self.baddfunc()  # execute external function before customization

    def bdel_action(self):
        if ismethod(self.bdelfunc):
            self.bdelfunc()  # execute external function before customization

    def spin_action(self):
        if ismethod(self.spinfunc):
            self.spinfunc()  # execute external function before customization

    def update_list(self, ulist, color_dict="", index=0):
        self.wlist.delete(0, tk.END)
        self._inlist = ulist
        self._gconfigure(ulist)
        self.gcolor(color_dict)
        # We can get 'index' that is None.  Default to position of last element of ulist.
        if not index or index >= len(ulist):
            index = len(ulist) - 1
        self.wlist.select_set(index)
        if len(ulist) > 0:
            self.bdel["state"] = self.bdel_default
        else:
            self.bdel["state"] = "disabled"

    def freeze(self, only_button="no"):
        if only_button == "no":
            self.wlist.configure(state="disabled")
        self.badd["state"] = "disabled"
        self.bdel["state"] = "disabled"
        # self.spin.configure(state='disabled')
        # self.spin_vip.configure(state='disabled')

    def unfreeze(self):
        self.wlist.configure(state="normal")
        self.badd["state"] = "normal"
        self.bdel["state"] = self.bdel_default
        # self.spin.configure(state='normal',bg='lightgrey')
        # self.spin_vip.configure(state='normal',bg='lightgrey')

    def set_reordering(self):
        self.wlist.configure(selectmode="extended")
        self.enable_reordering = 1

    def unset_reordering(self):
        self.wlist.configure(selectmode="browse")
        self.enable_reordering = 0

    def get_filter(self):
        # if self.spin_value:
        #   return self.spin.get()
        # else:
        return "ALL"

    def get_filter_vip(self):
        # if self.spin_vip_value:
        #   return self.spin_vip.get()
        # else:
        return "ALL"

    def get_index(self):
        if self.wlist.curselection():
            return self.wlist.curselection()[0]
        else:
            return None


class MyMenuWidget(tk.Menu):
    def __init__(
        self,
        master=None,
        MasterClass=None,
        savfunc="",
        loadfunc="",
        closefunc="",
        renamefunc="",
        lockfunc="",
        duplicate_itemfunc="",
        pref_save_func="",
        pref_color_func="",
        exitfunc="",
    ):
        tk.Menu.__init__(self, master)
        self.filemenu = tk.Menu(self, tearoff=0)
        self.editmenu = tk.Menu(self, tearoff=0)
        self.viewmenu = tk.Menu(self, tearoff=0)
        # self.exportmenu=tk.Menu(self,tearoff=0)
        self.prefmenu = tk.Menu(self, tearoff=0)
        self.editormenu = tk.Menu(self, tearoff=0)
        self.enable_reordering = tk.IntVar()
        self.editor_choice = tk.IntVar()
        self.editor_choice.set(EDITOR)
        self.menu_config(master)
        self.savfunc = savfunc
        self.loadfunc = loadfunc
        self.closefunc = closefunc
        self.exitfunc = exitfunc
        self.renamefunc = renamefunc
        self.lockfunc = lockfunc
        self.duplicate_itemfunc = duplicate_itemfunc
        self.MasterClass = MasterClass
        self.pref_save_func = pref_save_func
        self.pref_color_func = pref_color_func

    def menu_config(self, master):
        self.filemenu.add_command(label="--- Load       ", command=self.load)
        self.filemenu.add_command(label="--- Save       ", command=self.save)
        self.filemenu.add_command(label="--- Save As    ", command=self.save_as)
        self.filemenu.add_separator()
        self.filemenu.add_command(label="--- Close       ", command=self.close)
        self.filemenu.add_separator()
        self.filemenu.add_command(label="--- Exit       ", command=self.exitfunc)
        # self.exportmenu.add_separator()
        # self.exportmenu.add_command(label="--- Show Feature Statistics     ",command=self.export_ip_stat)
        self.viewmenu.add_command(
            label="--- Lock/Unlock Feature    ", command=self.lockfunc
        )
        self.viewmenu.add_separator()
        self.viewmenu.add_command(
            label="--- Rename Feature       ", command=self.renamefunc
        )
        self.viewmenu.add_command(
            label="--- Define Property Custom Numbering   ",
            command=self.set_prop_custom,
        )
        self.viewmenu.add_checkbutton(
            label="--- Enable Feature/Sub-Feature Reordering   ",
            onvalue=1,
            offvalue=0,
            variable=self.enable_reordering,
            command=self.reordering,
        )
        self.editmenu.add_command(
            label="--- Duplicate item       ", command=self.duplicate_itemfunc
        )
        self.editmenu.add_command(
            label="--- Copy and insert item ", command=self.insert_itemfunc
        )
        self.editormenu.add_checkbutton(
            label=" nedit  ",
            onvalue=1,
            variable=self.editor_choice,
            command=self.update_editor,
        )
        self.editormenu.add_checkbutton(
            label=" geany  ",
            onvalue=2,
            variable=self.editor_choice,
            command=self.update_editor,
        )
        self.editormenu.add_checkbutton(
            label=" gvim  ",
            onvalue=3,
            variable=self.editor_choice,
            command=self.update_editor,
        )
        self.editormenu.add_checkbutton(
            label=" gedit  ",
            onvalue=4,
            variable=self.editor_choice,
            command=self.update_editor,
        )
        self.add_cascade(label="File  ", menu=self.filemenu)
        self.add_cascade(label="Edit  ", menu=self.editmenu)
        self.add_cascade(label="Function  ", menu=self.viewmenu)
        # self.add_cascade(label="Export  ", menu=self.exportmenu)
        self.prefmenu.add_command(
            label="--- Color Settings  ", command=self.pref_color_func
        )
        self.prefmenu.add_cascade(label="--- Editor  ", menu=self.editormenu)
        self.prefmenu.add_separator()
        self.prefmenu.add_command(
            label="--- Save Preferences ", command=self.pref_save_func
        )
        self.add_cascade(label="Preferences  ", menu=self.prefmenu)

    def load(self):
        if ismethod(self.loadfunc):
            if self.loadfunc() == "yes":
                self.filemenu.entryconfig("--- Save       ", state="normal")

    def save(self):
        if ismethod(self.savfunc):
            self.savfunc()

    def save_as(self):
        if ismethod(self.savfunc):
            if self.savfunc(save_as="yes") == "yes":
                self.filemenu.entryconfig("--- Save       ", state="normal")

    def close(self):
        if ismethod(self.closefunc):
            if self.closefunc() == "yes":
                self.filemenu.entryconfig("--- Save       ", state="disabled")

    def exitfunc(self):
        if ismethod(self.exitfunc):
            if self.exitfunc() == "yes":
                self.exitfunc
        else:
            self.master.quit()

    def populate_ip(self):
        if ismethod(self.populatefunc):
            self.populatefunc()

    def set_prop_custom(self):
        global CUSTOM_NUM
        change_custom_name = tkinter.simpledialog.askstring(
            "Section Numbering",
            prompt="Specify a section custom numbering if needed",
            parent=self.MasterClass.top,
            initialvalue=CUSTOM_NUM,
        )
        if change_custom_name is not None:
            CUSTOM_NUM = change_custom_name

    def renamefunc(self):
        if ismethod(self.renamefunc):
            self.renamefunc()

    def reordering(self):
        if self.enable_reordering.get():
            self.MasterClass.ip_widget.set_reordering()
            self.MasterClass.prop_widget.set_reordering()
        else:
            self.MasterClass.ip_widget.unset_reordering()
            self.MasterClass.prop_widget.unset_reordering()

    # def export_ip_stat(self):
    #   if ismethod(self.exportIpStatfunc):
    #       self.exportIpStatfunc()
    def lockfunc(self):
        if ismethod(self.lockfunc):
            self.lockfunc()

    def duplicate_itemfunc(self):
        if ismethod(self.duplicate_itemfunc):
            self.duplicate_itemfunc(insert="no")

    def insert_itemfunc(self):
        if ismethod(self.duplicate_itemfunc):
            self.duplicate_itemfunc(insert="yes")

    def disable_edit(self):
        self.editmenu.entryconfigure(0, state=tk.DISABLED)
        self.editmenu.entryconfigure(1, state=tk.DISABLED)

    def enable_edit(self):
        self.editmenu.entryconfigure(0, state=tk.NORMAL)
        self.editmenu.entryconfigure(1, state=tk.NORMAL)

    def pref_save_func(self):
        if ismethod(self.pref_save_func):
            self.pref_save_func()

    def pref_color_func(self):
        if ismethod(self.pref_color_func):
            self.pref_color_func()

    def update_editor(self):
        global EDITOR
        EDITOR = self.editor_choice.get()


class MyTextWidget(ttk.LabelFrame):
    """
    This Widget contains:
            - several text boxes
            - buttons to validate/cancel text entering
            - several radio button rows
    """

    def __init__(
        self,
        master=None,
        parent=None,
        text="",
        expand=True,
        side=None,
        padx=1,
        pady=2,
        width=20,
        bsavefunc=None,
        bcancelfunc=None,
    ):
        ttk.LabelFrame.__init__(self, master, text=text)
        self.parent = parent

        enabledLabelFrame_style = ttk.Style()
        enabledLabelFrame_style.configure(
            "enabled.TLabelframe", foreground=SECONDARY_LABEL_COLOR
        )
        disabledLabelFrame_style = ttk.Style()
        disabledLabelFrame_style.configure(
            "disabled.TLabelframe", foreground=TERTIARY_LABEL_COLOR
        )
        self.textframe = ttk.LabelFrame(
            self,
            text=vp_config.yaml_config["gui"]["feature_descr"]["label"],
            style="enabled.TLabelframe",
        )
        self.text1frame = ttk.LabelFrame(
            self,
            text=vp_config.yaml_config["gui"]["requirement_loc"]["label"],
            style="enabled.TLabelframe",
        )
        # Design doc information uses a grid layout.
        # - first row is a URL of the document
        # - second row contains selectors for page/section mode and value, and a 'View' button.
        self.text1frame.grid(column=0, row=0, padx=20, pady=20)
        url_label = ttk.Label(self.text1frame, text="Path or URL", anchor=tk.E)
        url_label.grid(column=0, row=0, sticky=tk.E, padx=10, pady=10)
        mode_label = ttk.Label(self.text1frame, text="Refer to...", anchor=tk.E)
        mode_label.grid(column=0, row=1, sticky=tk.E, padx=10)
        self.page_num_var = tk.StringVar(self)
        page_entry = ttk.Entry(self.text1frame, textvariable=self.page_num_var, width=4)
        page_entry.grid(column=2, row=1, sticky=tk.W)
        # Use a callaback to update state upon changes to page number field.
        self.page_num_var.trace("w", self.ref_page_num_changed)

        self.section_num_var= tk.StringVar(self)
        section_entry = ttk.Entry(self.text1frame, textvariable=self.section_num_var, width=4)
        section_entry.grid(column=2, row=2, sticky=tk.W)
        # Use a callaback to update state upon changes to section number field.
        self.section_num_var.trace("w", self.ref_section_num_changed)

        view_btn = ttk.Button(self.text1frame, text="View design doc", command=self.view_design_doc)
        view_btn.grid(column=5, row=2, sticky=tk.E)
        self.ref_mode_var = tk.StringVar(self)
        ref_mode_names = ("(consecutive) page #", "section #")
        ref_mode_values = ("page", "section")
        row = 1
        for (name, value) in zip(ref_mode_names, ref_mode_values):
            btn = ttk.Radiobutton(self.text1frame, text=name, value=value, variable=self.ref_mode_var, command=self.refmode_btn_selected)
            btn.grid(column=1, row=row, sticky=tk.W)
            row +=1
        # Label of the viewer selector buttons
        viewer_label = ttk.Label(self.text1frame, text="Design doc viewer", anchor=tk.E)
        viewer_label.grid(column=3, row=1, sticky=tk.E)
        self.viewer_var = tk.StringVar(self)
        viewer_names = ("Mozilla Firefox", "Evince PDF viewer")
        viewer_values = ("firefox", "evince")
        row = 1
        for (name, value) in zip(viewer_names, viewer_values):
            btn = ttk.Radiobutton(self.text1frame, text=name, value=value, variable=self.viewer_var, command=self.docviewer_btn_selected)
            btn.grid(column=4, row=row, sticky=tk.W)
            row += 1

        self.text3frame = ttk.LabelFrame(
            self,
            text=vp_config.yaml_config["gui"]["verif_goals"]["label"],
            style="enabled.TLabelframe",
        )
        self.text4frame = ttk.LabelFrame(
            self,
            text=vp_config.yaml_config["gui"]["comments"]["label"],
            style="enabled.TLabelframe",
        )
        self.text5frame = ttk.LabelFrame(
            self,
            text=vp_config.yaml_config["gui"]["coverage_loc"]["label"],
            style="enabled.TLabelframe",
        )
        self.text6frame = ttk.LabelFrame(
            self,
            text=vp_config.yaml_config["gui"]["verif_tag"]["label"],
            style="enabled.TLabelframe",
        )
        # Selectors of verif point properties (PFC, TT, CM) and applicable cores use a layout
        # different from the surrounding widgets, so we pack them in a canvas of their own.
        self.selector_canvas = tk.Canvas(self)
        self.settings_frame = ttk.LabelFrame(
            self.selector_canvas,
            text="Verification Approach",
            style="enabled.TLabelframe",
        )
        self.pfc_frame = ttk.LabelFrame(
            self.settings_frame,
            text=vp_config.yaml_config["gui"]["pfc"]["label"],
            style="success.TLabelframe",
        )
        self.testtype_frame = ttk.LabelFrame(
            self.settings_frame,
            text=vp_config.yaml_config["gui"]["test_type"]["label"],
            style="enabled.TLabelframe",
        )
        self.covmethod_frame = ttk.LabelFrame(
            self.settings_frame,
            text=vp_config.yaml_config["gui"]["cov_method"]["label"],
            style="enabled.TLabelframe",
        )
        self.listofcores_frame = ttk.LabelFrame(
            self.selector_canvas, text="Applicable Cores", style="enabled.TLabelframe"
        )
        self.cores_all = tk.IntVar(self.listofcores_frame)
        self.cores_all_btn = tk.Checkbutton(
            self.listofcores_frame,
            text=vp_config.yaml_config["cores"]["default"]["label"],
            variable=self.cores_all,
            offvalue=0,
            onvalue=1,
            command=self.all_cores_btn_selected,
            state="active",
        )
        self.core_canvas = tk.Canvas(self.listofcores_frame)
        self.core_button = []
        self.num_cores = len(vp_config.yaml_config["cores"]["values"])
        for i in range(self.num_cores):
            entry = vp_config.yaml_config["cores"]["values"][i]
            intvar = tk.IntVar(self.core_canvas)
            btn = tk.Checkbutton(
                self.core_canvas,
                text=entry["label"],
                variable=intvar,
                offvalue=0,
                onvalue=1,
                command=self.core_btn_selected,
            )
            # Append a tuple (button widget, associated IntVar, associated bitmask).
            self.core_button.append(tuple([btn, intvar, entry["value"]]))

        # self.separator_v1 = ttk.Separator(self.selector_canvas, orient='vertical')
        self.separator_h2 = ttk.Separator(self.listofcores_frame, orient="horizontal")

        self.text = MyText(
            self.textframe,
            cue_text=vp_config.yaml_config["gui"]["feature_descr"]["cue_text"],
            state="disabled",
            height=6,
            bg=BG_COLOR,
            undo=True,
            wrap="word",
        )
        self.text1 = MyText(
            self.text1frame,
            cue_text=vp_config.yaml_config["gui"]["requirement_loc"]["cue_text"],
            state="disabled",
            height=2,
            bg=BG_COLOR,
            undo=True,
            wrap="word",
        )
        self.text1.grid(column=1, row=0, sticky=tk.W, columnspan=5)
        self.text3 = MyText(
            self.text3frame,
            cue_text=vp_config.yaml_config["gui"]["verif_goals"]["cue_text"],
            state="disabled",
            height=8,
            bg=BG_COLOR,
            undo=True,
            wrap="word",
        )
        self.text4 = MyText(
            self.text4frame,
            cue_text=vp_config.yaml_config["gui"]["comments"]["cue_text"],
            state="disabled",
            height=6,
            bg=BG_COLOR,
            undo=True,
            wrap="word",
        )
        self.text5 = MyText(
            self.text5frame,
            cue_text=vp_config.yaml_config["gui"]["coverage_loc"]["cue_text"],
            state="disabled",
            height=1,
            bg=BG_COLOR,
            undo=True,
            wrap="word",
        )
        self.text6 = MyText(
            self.text6frame,
            cue_text=vp_config.yaml_config["gui"]["verif_tag"]["cue_text"],
            state="disabled",
            height=1,
            bg=BG_COLOR,
            undo=False,
            wrap="word",
        )
        # Clear all key bindings but allow single-click to set focus
        # on the widget and double-click to select all.
        self.text6.unbind("<Key>")
        self.text6.bind("<1>", lambda event: self.text6.focus_set())

        self.pfc_string = tk.StringVar(self)
        self.testtype_string = tk.StringVar(self)
        self.covmethod_string = tk.StringVar(self)

        # By default, key events will be propagated to the following inner widgets:
        self.keyevent_notify_list = [
            self.text,
            self.text1,
            self.text3,
            self.text4,
            self.text5,
            # self.text6, # FOR NOW Not editable
        ]
        # By default, bulk text updates will be propagated to the following inner widgets:
        self.update_text_notify_list = self.keyevent_notify_list
        # button Frame
        self.bframe = ttk.Frame(self)
        self.bsave = ttk.Button(self.bframe, text="Save", command=self.bsave_action)
        self.bcancel = ttk.Button(
            self.bframe, text="Cancel", command=self.bcancel_action
        )

        # Walk the sorted list of possible PFC (Pass/Fail Criteria) entries.
        # Sorting is done on values associated with each PFC in the YAML file ==> the order of values defines the order of buttons.
        # Include the default value in the list of values.
        pfc_default = vp_config.yaml_config["gui"]["pfc"]["default"]
        self.pfc_entries = sorted(
            vp_config.yaml_config["gui"]["pfc"]["values"],
            key=lambda e: e["value"],
        )
        self.num_pfcs = len(self.pfc_entries)

        # Likewise for test type.
        testtype_default = vp_config.yaml_config["gui"]["test_type"]["default"]
        self.testtype_entries = sorted(
            vp_config.yaml_config["gui"]["test_type"]["values"],
            key=lambda e: e["value"],
        )
        self.num_testtypes = len(self.testtype_entries)

        # Likewise for coverage method.
        covmethod_default = vp_config.yaml_config["gui"]["cov_method"]["default"]
        self.covmethod_entries = sorted(
            vp_config.yaml_config["gui"]["cov_method"]["values"],
            key=lambda e: e["value"],
        )
        self.num_covmethods = len(self.covmethod_entries)

        # Create the PFC ComboBox
        self.pfc_string = tk.StringVar(self)
        self.pfc_cbox = ttk.Combobox(
            self.pfc_frame, textvariable=self.pfc_string, width=22
        )
        self.pfc_names = []
        for i in range(self.num_pfcs):
            self.pfc_names.append(self.pfc_entries[i]["label"])
        self.pfc_cbox["values"] = tuple([pfc_default["label"]] + self.pfc_names)
        self.pfc_cbox["state"] = "readonly"
        self.pfc_cbox.pack(side="left")
        self.pfc_cbox.bind("<<ComboboxSelected>>", self.pfc_cbox_selected)
        # Set default value
        self.pfc_cbox.set(pfc_default["label"])
        self.pfc = pfc_default["value"]

        # Create test type Combobox.
        self.testtype_cbox = ttk.Combobox(
            self.testtype_frame, textvariable=self.testtype_string, width=22
        )
        self.testtype_names = []
        for i in range(self.num_testtypes):
            self.testtype_names.append(self.testtype_entries[i]["label"])
        self.testtype_cbox["values"] = tuple(
            [testtype_default["label"]] + self.testtype_names
        )
        self.testtype_cbox["state"] = "readonly"
        self.testtype_cbox.pack(side="left")
        self.testtype_cbox.bind("<<ComboboxSelected>>", self.testtype_cbox_selected)
        # Set default value
        self.testtype_cbox.set(testtype_default["label"])
        self.test_type = testtype_default["value"]

        # Create coverage method Combobox.
        self.covmethod_cbox = ttk.Combobox(
            self.covmethod_frame, textvariable=self.covmethod_string, width=22
        )
        self.covmethod_names = []
        for i in range(self.num_covmethods):
            self.covmethod_names.append(self.covmethod_entries[i]["label"])
        self.covmethod_cbox["values"] = tuple(
            [covmethod_default["label"]] + self.covmethod_names
        )
        self.covmethod_cbox["state"] = "readonly"
        self.covmethod_cbox.pack(side="left")
        self.covmethod_cbox.bind("<<ComboboxSelected>>", self.covmethod_cbox_selected)
        # Set default value
        self.covmethod_cbox.set(covmethod_default["label"])
        self.cov_method = covmethod_default["value"]

        # Text3 Frame
        self.bsavefunc = bsavefunc
        self.bcancelfunc = bcancelfunc
        self.bsave.pack(side="left")
        self.bcancel.pack(side="left")
        self.pack(side, padx, pady)

    def ref_page_num_changed(self, *args):
        """React to change in page number stringvar."""
        current_item = self.parent.item_widget.get_selection()
        if current_item and not self.parent.get_current_item().is_locked():
            self.parent.get_current_item().ref_page = self.page_num_var.get()

    def ref_section_num_changed(self, *args):
        """React to change in section number stringvar."""
        current_item = self.parent.item_widget.get_selection()
        if current_item and not self.parent.get_current_item().is_locked():
            self.parent.get_current_item().ref_section = self.section_num_var.get()

    def view_design_doc(self):
        """
        View the requirement file (Design Doc) at the position specified in Requirement Location frame.
        """
        if self.viewer_var.get() == "firefox":
            # Browser mode: use HREFs with suffix #<anchortype>=<value>.
            if self.ref_mode_var.get() == "page":
                ref_in_doc = f"#page={self.page_num_var.get().rstrip()}"
            elif self.ref_mode_var.get() == "section":
                ref_in_doc = f"#nameddest=section.{self.section_num_var.get().rstrip()}"
            else:
                ref_in_doc = ""
            # Assume the location is a valid URL or an absolute path.
            doc_location = self.text1.get(0.0, tk.END).rstrip()
            # If no scheme (http://, file:// etc.) is given, treat it
            # as an absolute file path.
            if doc_location[0] == '/':
                doc_location = "file://" + doc_location
            command = [ "firefox", doc_location + ref_in_doc ]
        elif self.viewer_var.get() == "evince":
            # PDF viewer mode: use appropriate cmdline option.
            if self.ref_mode_var.get() == "page":
                ref_in_doc = ["-i", f"{self.page_num_var.get().rstrip()}" ]
            elif self.ref_mode_var.get() == "section":
                ref_in_doc = ["-n", f"section.{self.section_num_var.get().rstrip()}"]
            else:
                ref_in_doc = []
            # The requirement location should be a valid path to a PDF file.
            command = ["evince"] + ref_in_doc + [self.text1.get(0.0, tk.END).rstrip()]
        print(f"### ==> command = {command}")
        subprocess.Popen(command)

    def refmode_btn_selected(self):
        """
        Callback to handle the selection of the Design Doc reference mode.
        Sets the value of the corresponding item attribute.
        """
        current_item = self.parent.item_widget.get_selection()
        if current_item and not self.parent.get_current_item().is_locked():
            self.parent.get_current_item().ref_mode = self.ref_mode_var.get()

    def docviewer_btn_selected(self):
        """
        Callback to handle the selection of the design doc viewer.
        Sets the value of the corresponding item attribute.
        """
        current_item = self.parent.item_widget.get_selection()
        if current_item and not self.parent.get_current_item().is_locked():
            self.parent.get_current_item().ref_viewer = self.viewer_var.get()

    def all_cores_btn_selected(self):
        print("### self.cores_all.get() = %d" % self.cores_all.get())
        if self.cores_all.get() == 1:
            # Select all cores.
            current_item = self.parent.item_widget.get_selection()
            if current_item and not self.parent.get_current_item().is_locked():
                self.parent.get_current_item().cores = -1
                for i in range(self.num_cores):
                    self.core_button[i][1].set(1)
        else:
            # Leave per-core buttons unchanged.
            pass

    def core_btn_selected(self):
        mask = 0
        all_cores_set = True
        for i in range(self.num_cores):
            if self.core_button[i][1].get() == 1:
                mask |= self.core_button[i][2]
            else:
                # Uncheck the 'all' button.
                self.cores_all.set(0)
                all_cores_set = False
        # If all cores have their buttons cheched, switch to the 'All' mode.
        if all_cores_set:
            self.cores_all.set(1)
            mask = -1

        current_item = self.parent.item_widget.get_selection()
        if current_item and not self.parent.get_current_item().is_locked():
            self.parent.get_current_item().cores = mask
        # print('### core_btn_selected: mask = 0x%x' % mask)

    def pfc_cbox_selected(self, event):
        current_choice = self.pfc_cbox.get()
        if not current_choice.startswith(
            vp_config.yaml_config["gui"]["pfc"]["default"]["label"]
        ):
            pfcs = [
                e["value"] for e in self.pfc_entries if e["label"] == current_choice
            ]
            if pfcs:
                current_item = self.parent.item_widget.get_selection()
                if current_item and not self.parent.get_current_item().is_locked():
                    self.parent.get_current_item().pfc = pfcs[0]
            else:
                print("*** pfc_cbox_selected: Unknown value of PFC!")

    def testtype_cbox_selected(self, event):
        current = self.testtype_cbox.get()
        if not current.startswith(
            vp_config.yaml_config["gui"]["test_type"]["default"]["label"]
        ):
            testtypes = [
                e["value"] for e in self.testtype_entries if e["label"] == current
            ]
            if testtypes:
                current_item = self.parent.item_widget.get_selection()
                if current_item and not self.parent.get_current_item().is_locked():
                    self.parent.get_current_item().test_type = testtypes[0]
            else:
                print("*** testtype_cbox_selected: Unknown value of Test Type!")

    def covmethod_cbox_selected(self, event):
        current = self.covmethod_cbox.get()
        if not current.startswith(
            vp_config.yaml_config["gui"]["cov_method"]["default"]["label"]
        ):
            covmethods = [
                e["value"] for e in self.covmethod_entries if e["label"] == current
            ]
            if covmethods:
                current_item = self.parent.item_widget.get_selection()
                if current_item and not self.parent.get_current_item().is_locked():
                    self.parent.get_current_item().cov_method = covmethods[0]
            else:
                print("*** covmethod_cbox_selected: Unknown value of Coverage Method!")

    def pfc_cursor_shape(self, event):
        global DEFAULT_CURSOR, SPECIAL_CURSOR
        if self.pfc_label.cget("text") == " Implemented":
            self.pfc_label.configure(cursor=SPECIAL_CURSOR)
            self.pfc_label.configure(relief="raised")
        else:
            self.pfc_label.configure(cursor=DEFAULT_CURSOR)

    def testtype_cursor_shape(self, event):
        global DEFAULT_CURSOR, SPECIAL_CURSOR
        if self.testtype_label.cget("text") == " Implemented":
            self.testtype_label.configure(cursor=SPECIAL_CURSOR)
            self.testtype_label.configure(relief="raised")
        else:
            self.testtype_label.configure(cursor=DEFAULT_CURSOR)

    def covmethod_cursor_shape(self, event):
        global DEFAULT_CURSOR, SPECIAL_CURSOR
        if self.covmethod_label.cget("text") == " Implemented":
            self.covmethod_label.configure(cursor=SPECIAL_CURSOR)
            self.covmethod_label.configure(relief="raised")
        else:
            self.covmethod_label.configure(cursor=DEFAULT_CURSOR)

    def pfc_label_flatten(self, event):
        self.pfc_label.configure(relief="flat")

    def testtype_label_flatten(self, event):
        self.testtype_label.configure(relief="flat")

    def covmethod_label_flatten(self, event):
        self.covmethod_label.configure(relief="flat")

    def pack(self, side, padx, pady):
        self.text.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        #self.text1.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        self.text3.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        self.text4.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        self.text5.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        self.text6.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        # Define the final order of top-level Description sub-widgets.
        self.text1frame.pack(side="top", padx=padx, pady=pady, fill="both")
        self.textframe.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        self.text3frame.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        # The property selector canvas uses horizontal orientation (left-to-right).
        self.selector_canvas.pack(side="top", padx=padx, pady=pady, fill="both")
        self.settings_frame.pack(
            side="left", padx=padx, pady=pady, fill="both", expand=True
        )
        self.pfc_frame.pack(side="top", padx=padx, pady=pady, fill="none")
        self.testtype_frame.pack(side="top", padx=padx, pady=pady, fill="none")
        self.covmethod_frame.pack(side="top", padx=padx, pady=pady, fill="none")
        # List of applicable cores
        self.core_canvas.columnconfigure(0, weight=1)
        self.core_canvas.columnconfigure(1, weight=1)
        self.listofcores_frame.pack(
            side="left", padx=padx, pady=pady, fill="both", expand=True
        )
        self.cores_all_btn.pack(side="top", fill="x")
        self.separator_h2.pack(side="top", padx=padx, pady=pady, fill="both")
        self.core_canvas.pack(
            side="top", padx=padx, pady=pady, fill="both", expand=True
        )
        # Place per-core Checkbuttons.
        num_rows = (len(self.core_button) + 1) // 2
        for i in range(len(self.core_button)):
            elt = self.core_button[i]
            elt[0].grid(row=(i % num_rows), column=(i // num_rows), sticky=tk.W)

        self.text6frame.pack(side="top", padx=padx, pady=pady, fill="both")
        self.text5frame.pack(side="top", padx=padx, pady=pady, fill="both")
        self.text4frame.pack(side="top", padx=padx, pady=pady, fill="both", expand=True)
        self.bsave.pack(side="left")
        self.bcancel.pack(side="left")
        self.button_pack()
        self.button_pack_forget()

        ttk.LabelFrame.pack(
            self, expand=True, fill="both", side=side, padx=padx, pady=pady
        )

    # TODO FIXME: factorize
    def update_text(self, text_widget, mess):
        text_widget.delete("1.0", tk.END)
        if mess == "":
            text_widget.insert("1.0", text_widget.cue_text)
            text_widget.mark_set(tk.INSERT, "1.0")
            text_widget.configure(foreground=CUETEXT_COLOR)
        else:
            text_widget.insert(tk.INSERT, mess)
            text_widget.configure(foreground="black")
        text_widget.edit_reset()  # flush undo stack

    def bsave_action(self):
        if ismethod(self.bsavefunc):
            self.bsavefunc()  # execute external function before customization
            self.bframe.pack_forget()

    def bcancel_action(self):
        if ismethod(self.bcancelfunc):
            self.bcancelfunc()  # execute external function before customization
            self.bframe.pack_forget()

    def button_pack(self):
        self.bframe.pack(side="bottom")

    def button_pack_forget(self):
        self.bframe.pack_forget()

    def update_ref_mode(self, mode):
        self.ref_mode = mode
        self.ref_mode_var.set(mode)

    def update_page_num(self, page):
        self.page_num = page
        self.page_num_var.set(page)

    def update_section_num(self, section):
        self.section_num = section
        self.section_num_var.set(section)

    def update_viewer(self, viewer):
        self.viewer = viewer
        self.viewer_var.set(viewer)

    def update_item_tag(self, in_text):
        self.text6.configure(state="normal")
        self.text6.delete("1.0", tk.END)
        self.text6.insert("1.0", in_text)
        self.text6.configure(state="disabled")

    def update_prop_tag(self, in_text):
        # ZC: disable field
        # global LATEX_INSERT_MACRO
        # self.proptag.configure(state='normal')
        # self.proptag.delete(0,tk.END)
        # if in_text:
        #   self.proptag.insert(1,"\\"+LATEX_INSERT_MACRO+"{"+in_text+"}")
        # else:
        #   self.proptag.insert(1,in_text)
        # self.proptag.configure(state='readonly')
        pass

    def update_cores(self, cores):
        if cores == -1 or cores == (1 << self.num_cores) - 1:
            # -1 means verif item is applicable to all cores.
            # 'All-settable-bits-set" has the same meaning.
            self.cores_all.set(1)
            for i in range(self.num_cores):
                self.core_button[i][1].set(1)
        else:
            # Uncheck the all-cores button.
            self.cores_all.set(0)
            # Check/uncheck the buttons corresponding to individual cores.
            for i in range(self.num_cores):
                if cores & self.core_button[i][2] != 0:
                    self.core_button[i][1].set(1)
                else:
                    self.core_button[i][1].set(0)

    def update_pfc(self, pfc_num):
        self.pfc = pfc_num
        for i in range(self.num_pfcs):
            if pfc_num == self.pfc_entries[i]["value"]:
                # self.pfc_label.config(text=self.pfc_entries[i]['label'])
                self.pfc_cbox.set(self.pfc_entries[i]["label"])
                break
        # ZC TODO FIXME Add safeguard in case we reach this point without setting the string value.

    def update_testtype(self, testtype_num):
        self.test_type = testtype_num
        for i in range(self.num_testtypes):
            if testtype_num == self.testtype_entries[i]["value"]:
                # self.testtype_label.config(text=self.testtype_entries[i]['label'])
                self.testtype_cbox.set(self.testtype_entries[i]["label"])
                break
        # ZC TODO FIXME Add safeguard in case we reach this point without setting the label.

    def update_covmethod(self, covmethod_num):
        self.cov_method = covmethod_num
        for i in range(self.num_covmethods):
            if covmethod_num == self.covmethod_entries[i]["value"]:
                # self.covmethod_label.config(text=self.covmethod_entries[i]['label'])
                self.covmethod_cbox.set(self.covmethod_entries[i]["label"])
                break
        # ZC TODO FIXME Add safeguard in case we reach this point without setting the label.

    def enable(self):
        self.text.configure(state="normal")
        self.text1.configure(state="normal")
        self.text3.configure(state="normal")
        self.text4.configure(state="normal")
        self.text5.configure(state="normal")
        self.text6.configure(state="disabled")
        self.pfc_cbox.configure(state="normal")
        self.testtype_cbox["state"] = "normal"
        self.covmethod_cbox["state"] = "normal"
        self.cores_all_btn["state"] = "normal"
        for i in range(self.num_cores):
            self.core_button[i][0]["state"] = "normal"

    def disable(self):
        self.text.configure(state="disabled")
        self.text1.configure(state="disabled")
        self.text3.configure(state="disabled")
        self.text4.configure(state="disabled")
        self.text5.configure(state="disabled")
        self.text6.configure(state="disabled")
        self.pfc_cbox["state"] = "disabled"
        self.testtype_cbox["state"] = "disabled"
        self.covmethod_cbox["state"] = "disabled"
        self.cores_all_btn["state"] = "disabled"
        for i in range(self.num_cores):
            self.core_button[i][0]["state"] = "disabled"

    def clean(self):
        for widget in self.update_text_notify_list:
            self.update_text(widget, "")
        self.pfc = vp_config.yaml_config["gui"]["pfc"]["default"]["value"]
        self.pfc_cbox.set(vp_config.yaml_config["gui"]["pfc"]["default"]["label"])
        self.test_type = vp_config.yaml_config["gui"]["test_type"]["default"]["value"]
        self.testtype_cbox.set(
            vp_config.yaml_config["gui"]["test_type"]["default"]["label"]
        )
        self.test_type = vp_config.yaml_config["gui"]["cov_method"]["default"]["value"]
        self.covmethod_cbox.set(
            vp_config.yaml_config["gui"]["cov_method"]["default"]["label"]
        )

    ## lock feature
    def lock(self):
        self.disable()
        self.color_frame_text("disabled.TLabelframe")

    def unlock(self):
        self.enable()
        self.color_frame_text("enabled.TLabelframe")

    def color_frame_text(self, style):
        self.textframe.configure(style=style)
        self.text1frame.configure(style=style)
        self.pfc_frame.configure(style=style)
        self.testtype_frame.configure(style=style)
        self.covmethod_frame.configure(style=style)

    # Text
    def get_text_selection(self):
        text = ""
        try:
            text = self.text.selection_get()
        except:
            pass
        return text


class MyMain:
    """
    This is the Main class handling DB and GUI
    """

    def __init__(self, split_save=False):
        self.ip_list = {}
        self.top = ""
        self.vptool_gitrev = "$Id$"
        self.ip_widget = ""
        self.prop_widget = ""
        self.item_widget = ""
        self.verif_menu = ""
        self.desc_widget = ""
        self.op_checklist_dict = {}
        ## Selection Position History
        self.gui_item_history = {}
        self.gui_property_history = {}
        ##
        self.hold_state = 0  # Used to freeze List interface when entering test
        ##
        self.db_git_rev = ""
        # Save Config
        self.split_save = split_save

    #####################################
    ### Binding Functions
    def im_up_ip(self, event):
        # Update Locked ip list in real time (can be eventually be disabled for perf)
        self.load_lock_ip()
        if not self.hold_state:
            self.update_property_widget()

    def im_dc_ip(self, event):
        # No action for now.
        pass

    def im_up_ip_ctrl_lock(self, event):
        global LOCKED_IP_DICT
        self.lock_ip()
        self.ip_widget.gcolor(LOCKED_IP_DICT)

    def im_copy_ip(self, event):
        print(self.ip_widget.get_multiple_selection())

    ## Prop widget
    def im_up_prop(self, event):
        if not self.hold_state:
            self.update_item_widget()

    ## Item widget
    def im_up_item(self, event):
        if not self.hold_state:
            self.update_desc_widget()

    ## Desc widget
    def im_up_des_keypress(self, *args):
        for widget in self.desc_widget.keyevent_notify_list:
            cur_text = widget.get("1.0", tk.END)
            # print('### keypress: Size of text in "text" field = %d, last char code = %d' % (len(cur_text), ord(cur_text[-1])))
            # print('### keypress: Size of text in "text1" field = %d, last char code = %d' % (len(cur_text1), ord(cur_text1[-1])))
            # Check for typing if the field contains only the cue string.
            if (
                widget["state"] == "normal"
                and cur_text.startswith(widget.cue_text)
                and self.top.focus_get() == widget
            ):
                widget.delete("1.0", tk.END)
                widget.configure(fg="black")
        current_item = self.item_widget.get_selection()
        # Note it can be a int and not Ctrl key and item not locked
        if (
            current_item != ""
            and current_item != None
            and args[0].keycode != 37
            and args[0].keycode != 109
            and not self.get_current_item().is_locked()
            and not self.need_lock_ip()
        ):
            self.desc_widget.button_pack()
            if not self.hold_state:  # if not already in HOLD_STATE
                self.freeze_all()

    def im_up_desc_keyup(self, *args):
        for widget in self.desc_widget.keyevent_notify_list:
            cur_text = widget.get("1.0", tk.END)
            # print('### Size of text in "text" field = %d, last char code = %d' % (len(cur_text), ord(cur_text[-1])))
            # print('### Size of text in "text1" field = %d, last char code = %d' % (len(cur_text1), ord(cur_text1[-1])))
            # Check for the removal of entire cue string.
            if (
                widget["state"] == "normal"
                and cur_text == "\n"
                and self.top.focus_get() == widget
            ):
                widget.insert("1.0", widget.cue_text)
                widget.mark_set(tk.INSERT, "1.0")
                widget.configure(fg=CUETEXT_COLOR)

    def im_up_des_ctrl_lock(self, *args):
        current_item = self.item_widget.get_selection()
        if (
            current_item != ""
            and current_item != None
            and not self.hold_state
            and not self.need_lock_ip()
        ):  # Note it can be a int
            self.get_current_item().invert_lock()
            self.update_desc_widget()

    def im_up_des_tip_disp(self, *args):
        text = self.desc_widget.get_text_selection()
        if text and Item.is_tag_valid(text):
            text = text + ":\n\n" + self.get_item_by_tag(text).description
        elif self.get_current_item():
            text = (
                self.get_current_item().tag
                + ":\n\n"
                + self.get_current_item().description
            )
        self.desc_widget.tip_popup(text)

    ##Protect GUI exit through X button
    def main_exit_handler(self, *args):
        if tkinter.messagebox.askokcancel("Exit?", "Is Database Saved?\nReally Quit?"):
            self.top.quit()

    #####################################
    ### IP Section  #Note ip_list could be a class
    def create_ip(self):
        field_name = vp_config.yaml_config["gui"]["ip"]["label"]
        ip_name = tkinter.simpledialog.askstring(
            "New " + field_name,
            prompt="Enter %s to create" % field_name.lower(),
            parent=self.top,
        )
        ip_index = ""
        # if STANDALONE_VERIF:
        #   ip_index = tkinter.simpledialog.askstring('%s Index' % field_name,prompt='Enter %s index' % field_index.lower(),parent=self.top)
        # check name doesn't exist yet
        if ip_name in list(self.ip_list.keys()) or ip_name == "":
            tkinter.messagebox.showwarning(
                "Warning", "%s already existing" % field_name
            )
        # filter case when cancel is selected in tkSimpleDialog
        elif ip_name != None:
            self.ip_list[ip_name] = Ip(ip_name, ip_index)
            self.update_ip_widget()

    def delete_ip(self):
        """get current IP Object and delete it"""
        del self.ip_list[self.ip_widget.get_selection()]
        # flush_gui_history()
        self.update_ip_widget()

    def update_ip_widget(self):
        global LOCKED_IP_DICT
        # print "CHECK IP:",ip_list.keys()
        # sort IP by ip_num and put result into list_to_print
        index_to_set = self.ip_widget.get_index()
        key_sorted_by_ip_num = sorted(
            list(self.ip_list.values()),
            key=lambda ip: ip.wid_order
            if isinstance(ip.wid_order, int)
            else int(ip.wid_order, base=10),
        )
        list_to_print = []
        for ip_elt in key_sorted_by_ip_num:
            list_to_print.append(ip_elt.name)
        self.ip_widget.update_list(
            list_to_print, color_dict=LOCKED_IP_DICT, index=index_to_set
        )
        # TODO FIXME: Why do we need to re-color the IP list again here?
        self.ip_widget.gcolor(LOCKED_IP_DICT)
        self.update_property_widget()
        if list(self.ip_list.keys()):
            self.ip_widget.bdel[
                "state"
            ] = self.ip_widget.bdel_default  # IP deletion button enabled if existing IP
        else:
            self.ip_widget.bdel[
                "state"
            ] = "disabled"  # IP deletion button disabled if no IP

    def update_ip_name(self, old_name, new_name):
        if self.ip_list[old_name]:
            self.ip_list[new_name] = self.ip_list.pop(old_name)
            self.ip_list[new_name].name = new_name
        else:
            print("--- Warning: Ip not found")

    def need_lock_ip(self):
        global LOCKED_IP_DICT
        need_to_lock = False
        current_ip_name = self.ip_widget.get_selection()
        if current_ip_name in LOCKED_IP_DICT:
            if LOCKED_IP_DICT[current_ip_name] != pwd.getpwuid(os.getuid()).pw_name:
                need_to_lock = True
        else:
            need_to_lock = True
        return need_to_lock

    def is_locked_by_user(self, current_ip_name=""):
        global LOCKED_IP_DICT
        is_lock = 0
        if current_ip_name in LOCKED_IP_DICT:
            if LOCKED_IP_DICT[current_ip_name] == pwd.getpwuid(os.getuid()).pw_name:
                is_lock = 1
        return is_lock

    def get_current_ip(self):
        return self.ip_list[self.ip_widget.get_selection()]

    #####################################
    ### Property Section
    def create_prop(self):
        global CUSTOM_NUM
        """"""
        current_ip_name = self.ip_widget.get_selection()
        field_name = vp_config.yaml_config["gui"]["property"]["label"]
        prop_name = tkinter.simpledialog.askstring(
            "%s name" % field_name,
            prompt="Enter %s to create" % field_name.lower(),
            parent=self.top,
        )
        # Name existence check is done in IP class
        if prop_name != "" and prop_name != None:
            done = self.ip_list[self.ip_widget.get_selection()].add_property(
                prop_name, tag="", custom_num=CUSTOM_NUM
            )  # get current IP Object, and run create_property
            if not done:
                tkinter.messagebox.showwarning(
                    "Warning", "%s already existing" % field_name
                )
            self.update_property_widget()
        else:
            print("try again with a valid name")  ## to improve with popup

    def delete_prop(self):
        """ "get current IP Object, and delete its current property"""
        current_ip_name = self.ip_widget.get_selection()
        current_prop_name = self.prop_widget.get_selection()
        self.ip_list[current_ip_name].del_property(current_prop_name)
        # flush_gui_history()
        self.update_property_widget()

    def update_property_widget(self):
        global LOCKED_IP_DICT
        # print "update_property_widget"
        current_ip_name = self.ip_widget.get_selection()
        # re-enable GUI in case previous selected ip was locked
        self.prop_widget.unfreeze()
        self.item_widget.unfreeze()
        self.desc_widget.enable()
        if current_ip_name:
            key_sorted_by_prop_num = sorted(
                list(self.ip_list[current_ip_name].prop_list.values()),
                key=lambda prop: prop.wid_order,
            )
            list_to_print = []
            for prop_elt in key_sorted_by_prop_num:
                list_to_print.append(prop_elt.name)
            # get index to set if in line with history content
            if self.ip_widget.get_index() in self.gui_property_history:
                index_to_set = self.gui_property_history[self.ip_widget.get_index()]
            else:
                index_to_set = 0
            self.prop_widget.update_list(list_to_print, index=index_to_set)
            self.prop_widget.badd["state"] = "normal"
            if list(self.ip_list[current_ip_name].prop_list.keys()) == []:
                self.prop_widget.bdel[
                    "state"
                ] = "disabled"  # if no Property exists, disable del button
            else:
                self.prop_widget.bdel["state"] = "normal"
        else:
            self.prop_widget.update_list([])  # if no IP exists, clear Property
            self.prop_widget.badd[
                "state"
            ] = "disabled"  # if no IP exists, disable add/del button
            self.prop_widget.bdel["state"] = "disabled"
        self.update_item_widget()

    def list_all_prop(self):
        all_prop_list = []
        for ip in list(self.ip_list.values()):
            for prop in list(ip.prop_list.values()):
                all_prop_list.append(prop)
        return all_prop_list

    def get_current_prop(self):
        return self.ip_list[self.ip_widget.get_selection()].prop_list[
            self.prop_widget.get_selection()
        ]

    #####################################
    ### Item Section
    def create_item(self):
        """"""
        cur_prop = self.get_current_prop()  # get current IP/Prop object
        # To figure out the effective index of the newly added item
        # in update_item_widget, we need the actual item.
        new_item = cur_prop.add_item(tag=self.get_current_prop().tag)
        self.update_item_widget(cur_item=new_item)

    def delete_item(self):
        """"""
        current_item_name = self.item_widget.get_selection()
        self.get_current_prop().del_item(current_item_name)
        self.update_item_widget()

    def update_item_widget(self, cur_item=None):
        """
        Update the item widget based on the current set of items.
        If a new item was added, move the selection to that item prior
        to updating the fields so that the defaults of the new item
        are used instead of the values from the previously selected one.
        """
        current_ip_name = self.ip_widget.get_selection()
        current_prop_name = self.prop_widget.get_selection()
        # print('### top: current_ip_name = %s, current_prop_name = %s' % (current_ip_name, current_prop_name))
        ## Update List content
        if current_prop_name:
            ## Section: Filter selection to print depending on widget spinbox state
            fill_list = []
            filter_status = self.item_widget.get_filter()
            ## Apply first filter for VIP choice
            if self.item_widget.get_filter_vip() == "ALL":
                first_filtered_list = list(self.get_current_prop().item_list.values())
            elif self.item_widget.get_filter_vip() == "VIP":
                first_filtered_list = [
                    x
                    for x in list(self.get_current_prop().item_list.values())
                    if x.is_vip()
                ]
            else:  ##"ASSERTION"
                first_filtered_list = [
                    x
                    for x in list(self.get_current_prop().item_list.values())
                    if x.is_assert()
                ]
            ## Apply Second filter
            # Not done items only
            if filter_status == "VALIDATED":
                for i in [x for x in first_filtered_list if x.is_locked() == 1]:
                    fill_list.append(i.name)
            elif filter_status == "NOT VALIDATED":
                for i in [x for x in first_filtered_list if x.is_locked() == 0]:
                    fill_list.append(i.name)
            elif filter_status == "NOT DONE":
                for i in [
                    x
                    for x in first_filtered_list
                    if x.get_verif_status()[1] == " Not Done"
                ]:
                    fill_list.append(i.name)
            # Done items only
            elif filter_status == "DONE":
                for i in [
                    x
                    for x in first_filtered_list
                    if x.get_verif_status()[1] != " Not Done"
                ]:
                    fill_list.append(i.name)
            # All items
            else:
                # fill_list=self.get_current_prop().item_list.keys()
                for i in [x for x in first_filtered_list]:
                    fill_list.append(i.name)
            fill_list = sorted(fill_list)
            # get index to set if in line with history content
            if (
                self.ip_widget.get_index(),
                self.prop_widget.get_index(),
            ) in self.gui_item_history:
                index_to_set = self.gui_item_history[
                    (self.ip_widget.get_index(), self.prop_widget.get_index())
                ]
            else:
                index_to_set = 0
            # If we get called with a newly added item, override the index
            # with the position of the new item in order to set the selection
            # to that new item.
            if cur_item:
                for i in range(len(fill_list)):
                    if cur_item.name == fill_list[i]:
                        index_to_set = i
                        break
            self.item_widget.update_list(fill_list, index=index_to_set)
            self.desc_widget.update_prop_tag(self.get_current_prop().tag[3:])

        else:  # case: empty property list -> clean item list
            self.item_widget.update_list([])
            self.desc_widget.update_prop_tag("")
            self.item_widget.bdel["state"] = "disabled"
            self.item_widget.badd["state"] = "disabled"
        ## Update add button state
        if current_ip_name:
            if list(self.ip_list[current_ip_name].prop_list.keys()) == []:
                self.item_widget.badd[
                    "state"
                ] = "disabled"  # if no ip existing disable property/item creation
            else:
                self.item_widget.badd["state"] = "normal"
        self.update_desc_widget()
        self.update_menu_widget()

    def list_all_items(self, ip_to_parse=None):
        """
        Return a list of all items of the IP whose name is passed as argument.
        If no argument is fed, return all existing Items
        """
        all_item_list = []
        prop_to_parse = []
        if ip_to_parse in self.ip_list:
            prop_to_parse = list(self.ip_list[ip_to_parse].prop_list.values())
        elif ip_to_parse == None:
            prop_to_parse = self.list_all_prop()
        else:
            print("IP Not Defined")
        for prop in prop_to_parse:
            for item in list(prop.item_list.values()):
                all_item_list.append(item)
        return all_item_list

    def duplicate_item(self, insert="no"):
        """"""
        confirm = "no"
        current_item_name = self.item_widget.get_selection()
        if current_item_name and not self.need_lock_ip():
            current_item = self.get_current_item()
            if insert == "yes":
                confirm = tkinter.messagebox.askquestion(
                    "Reorder item numbering",
                    "Please take care while reordering items, Do you want to continue?",
                )
                if confirm == "yes":
                    self.get_current_prop().add_item(
                        tag=self.get_current_prop().tag,
                        description=current_item.description,
                        purpose=current_item.purpose,
                    )  # get current IP/Prop object
                    self.get_current_prop().insert_item(current_item_name)
            else:
                self.get_current_prop().add_item(
                    tag=self.get_current_prop().tag,
                    description=current_item.description,
                    purpose=current_item.purpose,
                )  # get current IP/Prop object
            self.update_item_widget()

    def get_item_by_tag(self, tag):
        """
        Return a item object from defined tag
        """
        match = Item()  # dummy item
        for ip in list(self.ip_list.values()):
            for prop in list(ip.prop_list.values()):
                for item in list(prop.item_list.values()):
                    if item.tag == tag:
                        match = item
        return match

    def get_current_item(self):
        try:
            return (
                self.ip_list[self.ip_widget.get_selection()]
                .prop_list[self.prop_widget.get_selection()]
                .item_list[self.item_widget.get_selection()]
            )
        except:
            return None

    #####################################
    ### Description Section
    def update_desc_widget(self):
        global LOCKED_IP_DICT
        current_item_name = self.item_widget.get_selection()
        if (
            current_item_name != "" and current_item_name != None
        ):  # Note it could be a int
            self.desc_widget.enable()
            current_item = self.get_current_item()
            # ZC: FIXME: Rework to hide internal structure of desc_widget.
            self.desc_widget.update_text(
                self.desc_widget.text, current_item.description
            )
            self.desc_widget.update_text(self.desc_widget.text1, current_item.purpose)
            self.desc_widget.update_text(
                self.desc_widget.text3, current_item.verif_goals
            )
            self.desc_widget.update_text(self.desc_widget.text4, current_item.comments)
            self.desc_widget.update_text(
                self.desc_widget.text5, current_item.coverage_loc
            )
            self.desc_widget.update_item_tag(current_item.tag)
            # Update mode of reference to location inside design doc.
            # DB migration: Assume 'page' as default if the field was not present.
            try:
                ref_mode = current_item.ref_mode
            except AttributeError:
                ref_mode = "page"
            self.desc_widget.update_ref_mode(ref_mode)
            # Update page number inside design doc.
            # DB migration: Assume empty string as default if the field was not present.
            try:
                ref_page = current_item.ref_page
            except AttributeError:
                ref_page = ""
            self.desc_widget.update_page_num(ref_page)
            # Update section number inside design doc.
            # DB migration: Assume empty string as default if the field was not present.
            try:
                ref_section = current_item.ref_section
            except AttributeError:
                ref_section = ""
            self.desc_widget.update_section_num(ref_section)
            # Update name of viewer app that should be used to display the design doc.
            # DB migration: Assume empty string as default if the field was not present.
            try:
                ref_viewer = current_item.ref_viewer
            except AttributeError:
                ref_viewer = "firefox"
            self.desc_widget.update_viewer(ref_viewer)

            pfc = current_item.pfc
            self.desc_widget.update_pfc(pfc)
            test_type = current_item.test_type
            self.desc_widget.update_testtype(test_type)
            cov_method = current_item.cov_method
            self.desc_widget.update_covmethod(cov_method)
            try:
                cores = current_item.cores
            except:
                current_item.cores = -1
                cores = -1
            self.desc_widget.update_cores(cores)

            if current_item.is_locked():
                self.desc_widget.lock()
            else:
                self.desc_widget.unlock()
        else:
            self.desc_widget.unlock()
            self.desc_widget.clean()
            self.desc_widget.disable()
        # if current selected ip is locked disable GUI
        if self.need_lock_ip():
            self.prop_widget.freeze(only_button="yes")
            self.item_widget.freeze(only_button="yes")
            self.desc_widget.disable()
        self.save_gui_history()

    def desc_save(self):
        # ZC: FIXME: Rework to hide internal structure of desc_widget.
        current_item = self.get_current_item()
        current_item.description = self.desc_widget.text.get(0.0, tk.END).rstrip()
        current_item.purpose = self.desc_widget.text1.get(0.0, tk.END).rstrip()
        current_item.verif_goals = self.desc_widget.text3.get(0.0, tk.END).rstrip()
        current_item.comments = self.desc_widget.text4.get(0.0, tk.END).rstrip()
        current_item.coverage_loc = self.desc_widget.text5.get(0.0, tk.END).rstrip()
        current_item.tag = self.desc_widget.text6.get(0.0, tk.END).rstrip()
        self.unfreeze_all()

    def desc_cancel(self):
        self.update_desc_widget()  # reprint current item initial value
        self.unfreeze_all()

    def update_ref_mode(self):
        self.get_current_item().ref_mode = self.desc_widget.ref_mode_var.get()
        self.desc_widget.update_ref_mode(self.desc_widget.ref_mode_var.get())

    def update_page_num(self):
        self.get_current_item().ref_page = self.desc_widget.page_num_var.get()
        self.desc_widget.update_page_num(self.desc_widget.page_num_var.get())

    def update_section_num(self):
        self.get_current_item().ref_section = self.desc_widget.section_num_var.get()
        self.desc_widget.update_section_num(self.desc_widget.section_num_var.get())

    def update_viewer(self):
        self.get_current_item().ref_viewer = self.desc_widget.viewer_var.get()
        self.desc_widget.update_viewer(self.desc_widget.viewer_var.get())

    def update_pfc(self):
        self.get_current_item().pfc = self.desc_widget.pfc.get()
        self.desc_widget.update_pfc(self.desc_widget.pfc.get())

    def update_testtype(self):
        self.get_current_item().test_type = self.desc_widget.test_type.get()
        self.desc_widget.update_testtype(self.desc_widget.test_type.get())

    def update_covmethod(self):
        self.get_current_item().cov_method = self.desc_widget.cov_method.get()
        self.desc_widget.update_covmethod(self.desc_widget.cov_method.get())

    def update_cores(self):
        if self.desc_widget.cores_all.get() == 1:
            mask = -1
        else:
            mask = 0
            for i in range(self.desc_widget.num_cores):
                if self.desc_widget.core_button[i][1].get() == 1:
                    mask |= self.desc_widget.core_button[i][2]
        self.get_current_item().cores = mask
        self.desc_widget.update_cores(mask)

    #####################################
    ### Menu Save and load

    def get_db_gitrev(self):
        """Get Git revision of database.
        Return 'files not in sync!' if all files do NOT share same SHA1."""
        # Check for Git coverage of all DB files.  Complain if
        # - some DB files are not under Git
        # - the files are not in sync (== belong in distinct commits.)
        db_filenames = []
        if self.split_save:
            dir_to_load = os.path.dirname(vp_config.SAVED_DB_LOCATION)
            db_filenames = glob.glob(dir_to_load + "/VP_IP*pck")
        else:
            db_filenames = [vp_config.SAVED_DB_LOCATION]
        working_dir = os.getcwd()
        ip_dir = os.path.dirname(vp_config.SAVED_DB_LOCATION)
        os.chdir(ip_dir)
        sha1_dict = OrderedDict()
        for db_fname in db_filenames:
            try:
                if subprocess.check_output(
                    "git ls-files " + db_fname, shell=True
                ).decode("utf-8"):
                    db_git_rev = (
                        subprocess.check_output("git log " + db_fname, shell=True)
                        .decode("utf-8")
                        .split(" ")[1]
                    )
                    if db_git_rev:
                        sha1_dict[db_fname] = db_git_rev
                else:
                    print(
                        "WARNING: DB file '%s' is not under Git version control!"
                        % db_fname
                    )
            except Exception as e:
                print(
                    "WARNING: Loaded DB is not under consistent git versioning (exception '%s')"
                    % str(e)
                )
        os.chdir(working_dir)
        return sha1_dict

    def save_db(self, save_as="no"):
        pickle_ip_list = []
        confirm = ""
        if self.ip_list:
            if save_as == "no":
                confirm = tkinter.messagebox.askquestion(
                    "Saving current Database", "Do you really want to Save?"
                )
            else:
                db_to_open = asksaveasfilename(initialdir=vp_config.VP_PLATFORM_TOP_DIR)
                if db_to_open:
                    open(db_to_open, "wb").close()  # create file to save
                    if os.path.exists(db_to_open):
                        vp_config.SAVED_DB_LOCATION = db_to_open
                        confirm = "yes"
            if confirm == "yes":
                # Verify db git version has not been updated since it was opened
                try:
                    current_db_revision = self.get_db_gitrev()
                except Exception as e:
                    print("*** save_db (git log check): exception: " + str(e))
                    print("INFO: Saved DB is not under Git versioning")
                    current_db_revision = self.db_git_rev
                if self.db_git_rev == current_db_revision or save_as != "no":
                    # change dict to list to improve predictability of asci output format for git versioning
                    self.clear_all_item_target_list()
                    self.prep_db_export()
                    # Sort IPs by ip_num for added stability.
                    pickle_ip_list = sorted(
                        list(self.ip_list.items()), key=lambda key: key[1].ip_num
                    )
                    # Create DVPLAN in Markdown format
                    md_dir = vp_config.MARKDOWN_OUTPUT_DIR
                    if os.path.isfile(md_dir):
                        print(
                            "*** MD destination '%s' is not a directory, cannot generate markdown output!"
                            % md_dir
                        )
                    else:
                        if not os.path.exists(md_dir):
                            try:
                                os.makedirs(md_dir)
                            except Exception as e:
                                print(
                                    "*** Cannot create markdown output directory '%s', output will be sent to database directory"
                                    % md_dir
                                )
                                md_dir = os.path.dirname(vp_config.SAVED_DB_LOCATION)
                        with open(
                            os.path.join(md_dir, "dvplan_")
                            + vp_config.PROJECT_IDENT
                            + ".md",
                            "w",
                        ) as md_file:
                            md_file.write("# Module: %s\n\n" % (vp_config.PROJECT_NAME))
                            for ip_elt in pickle_ip_list:
                                md_file.write(str(ip_elt[1]))
                                for rfu1_elt in ip_elt[1].rfu_list:
                                    md_file.write(str(rfu1_elt[1]))
                                    for rfu2_elt in rfu1_elt[1].rfu_list:
                                        # FORNOW Generate only when 'cores' include CV32A6-step1
                                        # (see sibling file 'vptool.yml').
                                        if rfu2_elt[1].cores & 8 != 0:
                                            md_file.write(str(rfu2_elt[1]))
                    if self.split_save:
                        save_dir = os.path.dirname(vp_config.SAVED_DB_LOCATION)
                        saved_ip_str = ""
                        for ip_elt in pickle_ip_list:
                            # Sign the IP with the current SHA1 of VPTOOL.
                            ip_elt[1].vptool_gitrev = self.vptool_gitrev
                            ip_elt[1].io_fmt_gitrev = vp_config.io_fmt_gitrev
                            ip_elt[1].config_gitrev = vp_config.config_gitrev
                            ip_elt[1].ymlcfg_gitrev = vp_config.yaml_config[
                                "yaml_cfg_gitrev"
                            ]
                            # Save individual IPs only if locked by user.
                            #if self.is_locked_by_user(current_ip_name=ip_elt[1].name):
                            #    saved_ip_str += "\n  " + ip_elt[1].name
                            #    with open(
                            #        save_dir
                            #        + "/VP_IP"
                            #        + str(ip_elt[1].ip_num).zfill(3)
                            #        + ".pck",
                            #        "wb",
                            #    ) as output:
                            #        pickle.dump(ip_elt, output, 0)
                            # TODO: Add translation of pickle_ip_list to new-gen
                            # types *HERE*, after emitting Pickle.
                            # Emit the Yaml output from the fixed structures,
                            # skipping pickled ones.
                            saved_ip_str += "\n  " + ip_elt[1].name
                            # Write yaml output
                            with open(
                                save_dir
                                + "/VP_IP"
                                + str(ip_elt[1].ip_num).zfill(3)
                                + ".yml",
                                "wb",
                            ) as output:
                                db_yaml_engine.dump(ip_elt[1].to_Feature(), output)

                        if saved_ip_str:
                            tkinter.messagebox.showinfo(
                                "Info",
                                "Following %s(s) saved: %s"
                                % (
                                    vp_config.yaml_config["gui"]["ip"]["label"].lower(),
                                    saved_ip_str,
                                ),
                            )
                        else:
                            tkinter.messagebox.showwarning(
                                "Warning",
                                "No %s(s) were locked and then saved"
                                % vp_config.yaml_config["gui"]["ip"]["label"].lower(),
                            )
                    else:
                        # ZC FIXME Add support for Yaml in non-split-save mode.
                        with open(vp_config.SAVED_DB_LOCATION, "wb") as output:
                            pickle.dump(len(pickle_ip_list), output, 0)
                            for ip_elt in pickle_ip_list:
                                pickle.dump(ip_elt, output, 0)
                    self.prep_db_import()
                    # update_ip_widget()
                    self.update_all_item_target_list()
                else:
                    tkinter.messagebox.showwarning(
                        "Warning",
                        "DB git revision has been updated behind our back! DB can not be saved! Initial/current hash set: see CONSOLE",
                    )
                    print(
                        "WARNING: DB git revision has been updated behind our back, DB can not be saved!\n"
                        + "\n\tInitial hash set = "
                        + str(self.db_git_rev)
                        + "\n"
                        + "\n\tNew hash set = "
                        + str(current_db_revision)
                    )
        else:
            tkinter.messagebox.showwarning("Warning", "Nothing to Save")
        return confirm

    def save_db_wrapper(self, *args):
        self.save_db(save_as="no")

    def load_db(
        self,
    ):
        need_to_load = ""
        if self.ip_list:
            need_to_load = tkinter.messagebox.askquestion(
                "Loading Database", "Close current DB and Load?"
            )
        else:
            need_to_load = "yes"
        if need_to_load == "yes":
            db_to_open = askopenfilename(initialdir=vp_config.VP_PLATFORM_TOP_DIR)
            if os.path.exists(str(db_to_open)):
                vp_config.SAVED_DB_LOCATION = db_to_open
                self.close_db_quiet()
                self.load_db_quiet()
                self.update_ip_widget()
            else:
                tkinter.messagebox.showwarning("Warning", "No DB Loaded!")
        return need_to_load

    def load_db_quiet(self, use_yaml_input=True):
        pickle_ip_list = []
        ip_num_next = 0
        if self.split_save:
            dir_to_load = os.path.dirname(vp_config.SAVED_DB_LOCATION)
            self.top.title(
                "%s: %s"
                % (
                    vp_config.yaml_config["gui"]["title"]
                    + " (project: "
                    + (
                        vp_config.PROJECT_NAME
                        if vp_config.PROJECT_NAME
                        else "<generic>"
                    )
                    + ")",
                    os.path.join(dir_to_load, "VP_IP[0-9][0-9][0-9].%s" % ("yml" if use_yaml_input else "pck")),
                )
            )
            if not use_yaml_input:
                for filename in glob.glob(dir_to_load + "/VP_IP[0-9][0-9][0-9].pck"):
                    # print("---INFO: Loading "+filename)
                    with open(filename, "rb") as input:
                        pickle_ip_list.append(pickle.load(input))
            else:
                for filename in glob.glob(dir_to_load + "/VP_IP[0-9][0-9][0-9].yml"):
                    with open(filename, "rb") as input:
                        pickle_ip_list.append(db_yaml_engine.load(input))
            if pickle_ip_list:
                # Find the lowest ip_num that can be used for newly created IPs.
                # It has to be higher than the highest existing ip_num.
                # Note: Explicit ip_nums can be strings iso. ints.
                ip_num_next = 1 + max(
                    [
                        (lambda e: e if isinstance(e, int) else int(e, base=10))(
                            elt.id if use_yaml_input # Yaml !!omap mode: list of objects
                            else elt[1].ip_num
                        )
                        for elt in pickle_ip_list
                    ]
                )
        else:
            # if a specific db to open is passed through argument update global var, for future saving
            self.top.title(
                "%s: %s"
                % (vp_config.yaml_config["gui"]["title"], vp_config.SAVED_DB_LOCATION)
            )
            with open(vp_config.SAVED_DB_LOCATION, "rb") as input:
                ip_num_next = pickle.load(
                    input
                )  # FIXME: This will fail if ip_num values are not contiguous.
                for dummy in range(ip_num_next):
                    pickle_ip_list.append(pickle.load(input))
        # change list to dict
        if use_yaml_input:
            # Yaml mode: !!omap yields a list of elts when loaded.
            for ip_elt in pickle_ip_list:
                self.ip_list[ip_elt.name] = ip_elt.to_Ip()
                # Seems pickle doesn't restore class attribute. Done manually here for IP
                self.ip_list[ip_elt.name].__class__._ip_count = ip_num_next
        else:
            # Pickle mode: list of objects is a list of mappings as 2-elt lists
            for ip_key, ip_elt in pickle_ip_list:
                self.ip_list[ip_key] = ip_elt
                # Seems pickle doesn't restore class attribute. Done manually here for IP
                self.ip_list[ip_key].__class__._ip_count = ip_num_next
        self.prep_db_import()
        self.update_all_item_target_list()
        self.db_git_rev = self.get_db_gitrev()

    def close_db(self):
        confirm = "no"
        if self.ip_list:
            confirm = tkinter.messagebox.askquestion(
                "Closing current Database", "Do you really want to Close Current Db?"
            )
            if confirm == "yes":
                self.close_db_quiet()
        return confirm

    def close_db_quiet(self):
        self.ip_list = {}
        Ip().__class__._ip_count = 0
        self.update_ip_widget()

    def prep_db_export(self):
        for ip in list(self.ip_list.values()):
            for prop in list(ip.prop_list.values()):
                prop.prep_to_save()
            ip.prep_to_save()

    def prep_db_import(self):
        for ip in list(self.ip_list.values()):
            for prop_elt in ip.rfu_list:
                prop_elt[1].post_load()
            ip.post_load()

    def rename_ip(self):
        initial_name = self.ip_widget.get_selection()
        new_name = tkinter.simpledialog.askstring(
            "Renaming IP",
            prompt="Specify a new name for IP",
            parent=self.top,
            initialvalue=initial_name,
        )
        if new_name:
            self.update_ip_name(initial_name, new_name)
            self.update_ip_widget()

    def lock_ip(self):
        global LOCKED_IP_DICT
        current_ip_name = self.ip_widget.get_selection()
        print("### lock_ip: Locked IPs before: " + str(LOCKED_IP_DICT))
        if current_ip_name in LOCKED_IP_DICT:
            if LOCKED_IP_DICT[current_ip_name] == pwd.getpwuid(os.getuid()).pw_name:
                LOCKED_IP_DICT.pop(current_ip_name)
            else:
                tkinter.messagebox.showwarning(
                    "Warning", "Ip is locked by " + LOCKED_IP_DICT[current_ip_name]
                )
        else:
            LOCKED_IP_DICT[current_ip_name] = pwd.getpwuid(os.getuid()).pw_name
        try:
            with open(vp_config.LOCKED_IP_LOCATION, "wb") as output:
                pickle.dump(LOCKED_IP_DICT, output, 0)
            self.update_ip_widget()
        except Exception as e:
            print(
                "WARNING: Locked Ip file has not been loaded (exception '%s')" % str(e)
            )
        print("### lock_ip: Locked IPs after: " + str(LOCKED_IP_DICT))

    def lock_all_ip(self):
        global LOCKED_IP_DICT
        print("### lock_all_ip: Locked IPs before: " + str(LOCKED_IP_DICT))
        for current_ip_name in self.ip_list:
            if current_ip_name in LOCKED_IP_DICT:
                if LOCKED_IP_DICT[current_ip_name] == pwd.getpwuid(os.getuid()).pw_name:
                    LOCKED_IP_DICT.pop(current_ip_name)
                else:
                    tkinter.messagebox.showwarning(
                        "Warning", "Ip is locked by " + LOCKED_IP_DICT[current_ip_name]
                    )
            else:
                LOCKED_IP_DICT[current_ip_name] = pwd.getpwuid(os.getuid()).pw_name
            try:
                with open(vp_config.LOCKED_IP_LOCATION, "wb") as output:
                    pickle.dump(LOCKED_IP_DICT, output, 0)
                self.update_ip_widget()
            except Exception as e:
                print(
                    "WARNING: Locked Ip file has not been loaded (exception '%s')"
                    % str(e)
                )
        print("### lock_all_ip: Locked IPs after: " + str(LOCKED_IP_DICT))

    def load_lock_ip(self):
        global LOCKED_IP_DICT
        LOCKED_IP_DICT = {}
        print("### load_lock_ip: Locked IPs before: " + str(LOCKED_IP_DICT))
        try:
            with open(vp_config.LOCKED_IP_LOCATION, "rb") as input:
                LOCKED_IP_DICT = pickle.load(input)
            self.ip_widget.gcolor(LOCKED_IP_DICT)
        except Exception as e:
            print(
                "WARNING: Locked Ip file has not been loaded (exception '%s')" % str(e)
            )
        print("### load_lock_ip: Locked IPs after: " + str(LOCKED_IP_DICT))

    def update_menu_widget(self):
        global ip_list
        current_item_name = self.item_widget.get_selection()
        if current_item_name and not self.need_lock_ip():
            self.verif_menu.enable_edit()
        else:
            self.verif_menu.disable_edit()

    def freeze_all(self):
        self.ip_widget.freeze()
        self.prop_widget.freeze()
        self.item_widget.freeze()
        self.hold_state = 1

    def unfreeze_all(self):
        self.hold_state = 0
        self.ip_widget.unfreeze()
        self.prop_widget.unfreeze()
        self.item_widget.unfreeze()

    def export_new_order(self, reference_list):
        current_ip_name = self.ip_widget.get_selection()
        if self.ip_widget.need_to_reorder:
            for i, elt in enumerate(reference_list):
                self.ip_list[elt].wid_order = i
            self.ip_widget.need_to_reorder = 0
            self.update_property_widget()
        elif self.prop_widget.need_to_reorder:
            for i, elt in enumerate(reference_list):
                self.ip_list[current_ip_name].prop_list[elt].wid_order = i
            self.prop_widget.need_to_reorder = 0
            self.update_item_widget()

    def try_str_to_float(self, string):
        """if possible cast string into float"""
        try:
            return float(string)
        except:
            return string

    def personalization(self):
        """Get information of personalization if existing"""
        global PERSO_FILE, BG_COLOR, EDITOR
        if os.path.exists(sys.argv[0]):
            dir_path = os.path.dirname(sys.argv[0])
            if os.path.exists(dir_path + "/" + PERSO_FILE):
                with open(dir_path + "/" + PERSO_FILE, "rb") as input:
                    BG_COLOR = pickle.load(input)
                    EDITOR = pickle.load(input)

    def save_personalization(self):
        """Save information of personalization"""
        global PERSO_FILE
        if os.path.exists(sys.argv[0]):
            preference_file = os.path.dirname(sys.argv[0]) + "/" + PERSO_FILE
            with open(preference_file, "wb") as output:
                pickle.dump(BG_COLOR, output, 0)
                pickle.dump(EDITOR, output, 0)
                pickle.dump(self.verif_menu.enable_image_panel.get(), output, 0)

    def change_gui_color(self):
        global BG_COLOR
        BG_COLOR = tkinter.colorchooser.askcolor(color=BG_COLOR)[1]
        self.desc_widget.text.configure(bg=BG_COLOR)
        self.desc_widget.text1.configure(background=BG_COLOR)
        self.ip_widget.wlist.configure(background=BG_COLOR)
        self.prop_widget.wlist.configure(background=BG_COLOR)
        self.item_widget.wlist.configure(background=BG_COLOR)
        self.update_ip_widget()

    def save_gui_history(self):
        """
        Save current selection to history
        """
        if self.prop_widget.get_index():
            prop_index = self.prop_widget.get_index()
        else:
            prop_index = 0
        if self.item_widget.get_index():
            item_index = self.item_widget.get_index()
        else:
            item_index = 0
        if self.ip_widget.get_index():
            ip_index = self.ip_widget.get_index()
        else:
            ip_index = 0
        self.gui_property_history[ip_index] = prop_index
        self.gui_item_history[(ip_index, prop_index)] = item_index

    def flush_gui_history(self):
        """
        Flush all history content
        Used as soon as ip/prop are deleted
        Can be improved to flush only required elements
        """
        self.gui_property_history = {}
        self.gui_item_history = {}

    def unlock_db(self):
        for ip in list(self.ip_list.values()):
            ip.unlock_ip()

    def update_all_item_target_list(self):
        pass

    def clear_all_item_target_list(self):
        """Clear rfu_dict -not needed to be saved- for output base format predictability"""
        for ip in list(self.ip_list.values()):
            ip.rfu_dict = {}

    # FIXME: Can go.
    def get_spin_vip_config(self):
        spin_vip_config = ("ALL", "VIP")
        return spin_vip_config

    #####################################
    ##### DB INTERACTIION FUNCTIONS

    ##### Main GUI Creation
    def create_gui(self, theme, use_yaml_input):
        self.personalization()

        # TOP Widget
        self.top = themed_tk.ThemedTk(toplevel=True, className="cv-vptool")
        self.theme = theme
        self.style = ttk.Style(self.top)
        available_themes = self.top.get_themes()
        fallback_theme = vp_config.yaml_config["gui"]["theme"]
        print(
            '### Available themes: %s, using "%s" as fallback...'
            % (available_themes, fallback_theme)
        )
        if self.theme not in available_themes:
            self.theme = fallback_theme
        self.style.theme_use(self.theme)

        self.top.title(
            vp_config.yaml_config["gui"]["title"]
            + ": "
            + (
                vp_config.PROJECT_NAME
                if vp_config.PROJECT_NAME
                else "<generic project>"
            )
        )
        self.top.minsize(1200, 660)

        self.icon = ImageTk.PhotoImage(
            file=os.path.join(os.path.dirname(__file__), "vptool-icon.ico")
        )
        self.top.iconphoto(True, self.icon)
        # IP Widget
        self.ip_widget = MyListWidget(
            master=self.top,
            MasterClass=self,
            reflist=list(self.ip_list.keys()),
            text=vp_config.yaml_config["gui"]["ip"]["label"],
            side="left",
            expand="no",
            baddfunc=self.create_ip,
            bdelfunc=self.delete_ip,
            bdel_default="disabled",
        )
        self.ip_widget.badd["state"] = "normal"  # IP creation button enabled
        # Property Widget
        self.prop_widget = MyListWidget(
            master=self.top,
            MasterClass=self,
            text=vp_config.yaml_config["gui"]["property"]["label"],
            side="left",
            expand="no",
            baddfunc=self.create_prop,
            bdelfunc=self.delete_prop,
            width=35,
        )
        # Item Widget
        self.item_widget = MyListWidget(
            master=self.top,
            MasterClass=self,
            text=vp_config.yaml_config["gui"]["item"]["label"],
            side="left",
            expand="no",
            baddfunc=self.create_item,
            bdelfunc=self.delete_item,
            width=6,
            spinfunc=self.update_item_widget,
            spin_value=None,
            spin_vip_value=None,
        )
        self.verif_menu = MyMenuWidget(
            master=self.top,
            MasterClass=self,
            savfunc=self.save_db,
            loadfunc=self.load_db,
            closefunc=self.close_db,
            renamefunc=self.rename_ip,
            lockfunc=self.lock_ip,
            duplicate_itemfunc=self.duplicate_item,
            pref_save_func=self.save_personalization,
            pref_color_func=self.change_gui_color,
            exitfunc=self.main_exit_handler,
        )
        self.top.config(menu=self.verif_menu)
        # Test Description Widget
        self.desc_widget = MyTextWidget(
            master=self.top,
            parent=self,
            text=vp_config.yaml_config["gui"]["test_descr"]["label"],
            side="top",
            bsavefunc=self.desc_save,
            bcancelfunc=self.desc_cancel,
        )
        # Layout

        ## Bindings
        self.ip_widget.wlist.bind("<<ListboxSelect>>", self.im_up_ip)
        self.ip_widget.wlist.bind("<Double-Button-1>", self.im_dc_ip)
        self.ip_widget.wlist.bind("<Control-1>", self.im_up_ip_ctrl_lock)
        self.prop_widget.wlist.bind("<<ListboxSelect>>", self.im_up_prop)
        for widget in self.desc_widget.keyevent_notify_list:
            widget.bind("<KeyPress>", self.im_up_des_keypress)
        for widget in self.desc_widget.keyevent_notify_list:
            widget.bind("<KeyRelease>", self.im_up_desc_keyup)
        self.desc_widget.text.bind("<Control-1>", self.im_up_des_ctrl_lock)
        self.desc_widget.text1.bind("<Control-1>", self.im_up_des_ctrl_lock)
        self.desc_widget.text.bind("<Control-3>", self.im_up_des_tip_disp)
        self.item_widget.wlist.bind("<<ListboxSelect>>", self.im_up_item)
        self.load_db_quiet(use_yaml_input)
        self.load_lock_ip()
        self.update_ip_widget()
        self.top.bind("<Control-q>", self.main_exit_handler)
        self.top.bind("<Control-s>", self.save_db_wrapper)
        self.top.protocol("WM_DELETE_WINDOW", self.main_exit_handler)
        # Save Config
        # self.split_save = True
        if __name__ == "__main__":
            self.top.mainloop()


#####################################
##### MAIN
def __generate_option_parser():
    parser = OptionParser()
    parser.add_option(
        "-d",
        "--db",
        dest="dataBase",
        help="Specify a DataBase to load",
        default="empty",
        metavar="DATABASE",
    )
    parser.add_option(
        "-t",
        "--theme",
        dest="theme",
        help="Select a GUI theme for this session",
        default=vp_config.yaml_config["gui"]["theme"],
    )
    parser.add_option(
        "-y",
        "--yaml",
        action="store_true",
        dest="use_yaml_input",
        help="Read database in Yaml format",
        default=True,
    )
    parser.add_option(
        "-p",
        "--pickle",
        action="store_false",
        dest="use_yaml_input",
        help="Read database in Pickle format",
        default=True,
    )

    return parser


# Load YAML configuration if available.
try:
    with open(os.path.join(os.path.dirname(__file__), YAML_CONFIG_FILE), "r") as f:
        config_yaml_engine = YAML(typ='safe')
        vp_config.init_yaml_config(config_yaml_engine.load(f))
        # print("YAML config = \n" + dump(vp_config.yaml_config, Dumper=Dumper))
except Exception as e:
    print(
        "Cannot load YAML configuration file '%s' (exception: %s)"
        % (YAML_CONFIG_FILE, str(e))
    )
    sys.exit(1)

parser = __generate_option_parser()
(options, args) = parser.parse_args(sys.argv)

top_gui = MyMain(split_save=vp_config.SPLIT_SAVE)

# get db to use from arguments
if os.path.exists(os.path.realpath(options.dataBase)):
    SAVED_DB_LOCATION = os.path.realpath(options.dataBase)
    print(SAVED_DB_LOCATION)

top_gui.create_gui(options.theme, options.use_yaml_input)
