#! /usr/bin/env python3
## 
## Copyright 2021 OpenHW Group
## Copyright 2021 Datum Technology Corporation
## SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
## 
## Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
## not use this file except in compliance with the License, or, at your option,
## the Apache License version 2.0. You may obtain a copy of the License at
## 
##     https://solderpad.org/licenses/SHL-2.1/
## 
## Unless required by applicable law or agreed to in writing, any work
## distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
## WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
## License for the specific language governing permissions and limitations
## under the License.
## 



"""Design Verification \'Makefile\'.

Usage:
  dvm.py all  <target>  [-t <test_name>]  [-s <seed>]  [-g | --gui]  [-d | --debug]  [-w | --waves] [-q | --noclean]
  dvm.py cmp  <target>
  dvm.py elab <target>  [-d | --debug]
  dvm.py cpel <target>
  dvm.py sim  <target>  [-t <test_name>]  [-s <seed>]  [-g | --gui]  [-w | --waves]
  dvm.py clean
  dvm.py update
  dvm.py (-h | --help)
  dvm.py --version

Example:
  dvm.py all uvmt_obi_st -t all_access -s 1

Options:
  -h --help     Show this screen.
  --version     Show version.

"""



from docopt     import docopt
import sys
import os
import glob
import subprocess
import shutil
from os import path
import stat

if (sys.version_info < (3,0,0)):
    print ('Requires python 3')
    exit(1)

dbg = False
pwd             = os.getcwd()
uvm_dpi_so      = "uvm_dpi"
project_dir     = pwd + "/../../../../"
rtl_path        = project_dir + "/rtl"
rtl_libs_path   = rtl_path + "/.imports"
uvm_agents_path = project_dir + "/lib/uvm_agents"
dv_imports_path = project_dir + "/lib/uvm_libs/mio"
sim_debug       = False
sim_gui         = False
sim_waves       = False

vivado_path     = os.environ.get('VIVADO_PATH')
if (vivado_path == None):
    vivado_path = "/tools/Xilinx/Vivado/2020.2/bin/"   
    #vivado_path = "C:/Xilinx/Vivado/2020.3/bin/"
    if (dbg):
        print ("VIVADO_PATH env var *not* set, using " + vivado_path)
else:
    if (dbg):
        print ("VIVADO_PATH env var is " + vivado_path)


def do_dispatch(args):
    glb_args = args
    
    if (dbg):
        print("Call to do_dispatch()")
    do_paths()
    
    if not args['<seed>']:
        args['<seed>'] = 1
    
    if args['update']:
        args['clean'] = False
        args['cmp'  ] = False
        args['elab' ] = False
        args['sim'  ] = False
    
    if args['all']:
        args['cmp'  ] = True
        args['elab' ] = True
        args['sim'  ] = True
        if (args['-q'] or args['--noclean']):
            args['clean'] = False
        else:
            args['clean'] = True
    
    if args['cpel']:
        args['clean'] = True
        args['cmp'  ] = True
        args['elab' ] = True
        args['sim'  ] = False
    
    if (args['-d'] or args['--debug']):
        sim_debug = True
    else:
        sim_debug = False
    
    if (args['-w'] or args['--waves']):
        sim_waves = True
        sim_debug = True
    else:
        sim_waves = False
    
    if (args['-g'] or args['--gui']):
        sim_debug = True
        sim_gui   = True
    else:
        sim_gui   = False
    
    if args['clean']:
        do_clean()
    if args['cmp']:
        out_path = pwd + "/out"
        if not os.path.exists(out_path):
            os.mkdir(out_path)
        do_cmp_rtl(args['<target>'])
        do_cmp_dv (uvm_agents_path + "/" + args['<target>'] + "/src/" + args['<target>'] + "_pkg.flist.xsim", args['<target>'])
    if args['elab']:
        do_elab_rtl(args['<target>'])
        do_elab_dv (args['<target>'], args['<target>'] + "_tb")
    if args['sim']:
        do_sim(args['<target>'] + "_tb", args['<target>'] + "_" + args['<test_name>'] + "_test", args['<seed>'], [])
    if args['update']:
        do_update()



def do_paths():
    if (dbg):
        print("Call to do_paths()")
    
    ### RTL ###
    set_env_var("RTL_PKT_SNF_PATH", rtl_path + "/pkt_snf")
    
    ### DV ###
    # Libraries
    set_env_var("UVM_HOME"                 , dv_imports_path + "/uvm"                   )
    set_env_var("DV_UVM_SRC_PATH"          , dv_imports_path + "/uvm"           + "/src")
    set_env_var("DV_UVML_HRTBT_SRC_PATH"   , dv_imports_path + "/uvml_hrtbt"    + "/src")
    set_env_var("DV_UVML_TRN_SRC_PATH"     , dv_imports_path + "/uvml_trn"      + "/src")
    set_env_var("DV_UVML_LOGS_SRC_PATH"    , dv_imports_path + "/uvml_logs"     + "/src")
    set_env_var("DV_UVML_IO_SRC_PATH"      , dv_imports_path + "/uvml_io"       + "/src")
    set_env_var("DV_UVML_SB_SRC_PATH"      , dv_imports_path + "/uvml_sb"       + "/src")
    set_env_var("DV_UVML_RAL_SRC_PATH"     , dv_imports_path + "/uvml_ral"      + "/src")
    set_env_var("DV_UVMA_RESET_SRC_PATH"   , dv_imports_path + "/uvma_reset"    + "/src")
    set_env_var("DV_UVME_RESET_ST_SRC_PATH", dv_imports_path + "/uvme_reset_st" + "/src")
    set_env_var("DV_UVMT_RESET_ST_SRC_PATH", dv_imports_path + "/uvmt_reset_st" + "/src")
    set_env_var("DV_UVMA_CLK_SRC_PATH"     , dv_imports_path + "/uvma_clk"      + "/src")
    set_env_var("DV_UVME_CLK_ST_SRC_PATH"  , dv_imports_path + "/uvme_clk_st"   + "/src")
    set_env_var("DV_UVMT_CLK_ST_SRC_PATH"  , dv_imports_path + "/uvmt_clk_st"   + "/src")
    set_env_var("DV_UVMA_AXIL_SRC_PATH"    , dv_imports_path + "/uvma_axil"     + "/src")
    set_env_var("DV_UVME_AXIL_ST_SRC_PATH" , dv_imports_path + "/uvme_axil_st"  + "/src")
    set_env_var("DV_UVMT_AXIL_ST_SRC_PATH" , dv_imports_path + "/uvmt_axil_st"  + "/src")
    
    # Source
    set_env_var("DV_UVMA_OBI_MEMORY_SRC_PATH"   , uvm_agents_path + "/uvma_obi_memory"    + "/src")
    set_env_var("DV_UVME_OBI_ST_SRC_PATH", uvm_agents_path + "/uvme_obi_st" + "/src")
    set_env_var("DV_UVMT_OBI_ST_SRC_PATH", uvm_agents_path + "/uvmt_obi_st" + "/src")


def set_env_var(name, value):
    if (dbg):
        print("Setting env var '" + name + "' to value '" + value + "'")
    os.environ[name] = value



def do_clean():
    if (dbg):
        print("Call to do_clean()")
    print("********")
    print("Cleaning")
    print("********")
    if os.path.exists("./xsim.dir"):
        shutil.rmtree("./xsim.dir")
    if os.path.exists("./out"):
        shutil.rmtree("./out")
    if os.path.exists("__pycache__"):
        shutil.rmtree("__pycache__")
    if os.path.exists("results"):
        shutil.rmtree("results")
    if os.path.exists("uvmt_obi_st"):
        shutil.rmtree("uvmt_obi_st")
    jous = glob.glob('*.jou')
    for jou in jous:
        os.remove(jou)
    logs = glob.glob('*.log')
    for log in logs:
        os.remove(log)
    pbs = glob.glob('*.pb')
    for pb in pbs:
        os.remove(pb)
    wdbs = glob.glob('*.wdb')
    for wdb in wdbs:
        os.remove(wdb) 



def do_cmp_rtl(target_design):
    if (dbg):
        print("Call to do_cmp_rtl(target_design='" + target_design + "'")
    
    



def do_cmp_dv(filelist_path, lib_name):
    #if (dbg):
    print("Call to do_cmp_dv(filelist_path='" + filelist_path + "', lib_name='" + lib_name + "')")
    print("************")
    print("Compiling DV")
    print("************")
    
    run_xsim_bin("xvlog", "--incr -sv -f " + filelist_path + " -L uvm --work " + lib_name + "=" + lib_name + " --log ./out/compilation.log")



def do_elab_rtl(target_design):
    if (dbg):
        print("Call to do_elab_rtl(target_design='" + target_design + "')")
    
    


def do_elab_dv(lib_name, design_unit):
    
    debug_str = ""
    
    if (dbg):
        print("Call to do_elab_dv(lib_name='" + lib_name + "', design_unit='" + design_unit + "')")
    print("**************")
    print("Elaborating DV")
    print("**************")
    
    if (sim_debug):
        debug_str = " --debug all "
    else:
        debug_str = ""
    
    run_xsim_bin("xelab", lib_name + "." + design_unit + " " + lib_name + "." + "uvml_logs_sim_summary " + debug_str + " --incr -relax --O0 -v 0 -s " + design_unit + " -timescale 1ns/1ps -L " + lib_name + "=" + lib_name + " --log ./out/elaboration.log")
    



def do_sim(snapshot, test_name, seed, args):
    
    waves_str = ""
    gui_str   = ""
    runall_str   = ""
    
    args.append("SIM_DIR_RESULTS=" + pwd + "/results")
    args.append("UVM_TESTNAME=" + test_name + "_c")
    
    act_args = ""
    for arg in args:
        act_args = act_args + " -testplusarg \"" + arg + "\""
    
    if not os.path.exists(pwd + "/results/"):
        os.mkdir(pwd + "/results/")
    
    tests_results_path = pwd + "/results/" + test_name + "_" + str(seed)
    if not os.path.exists(tests_results_path):
        os.mkdir(tests_results_path)

    
    if (dbg):
        print("Call to do_sim(snapshot='" + snapshot + "', test_name='" + test_name + "', seed='" + str(seed) + "', args='" + act_args + "')")
    
    print("**********")
    print("Simulating")
    print("**********")
    
    if (sim_waves):
        if not os.path.exists(tests_results_path + "/waves_cfg.tcl"):
            f = open(tests_results_path + "/waves_cfg.tcl", "w")
            f.write("log_wave -recursive *")
            f.write("\n")
            f.write("run -all")
            f.write("\n")
            f.write("quit")
            f.close()
        waves_str = " --wdb " + tests_results_path + "/waves.wdb --tclbatch " + tests_results_path + "/waves_cfg.tcl"
    else:
        waves_str = ""
    
    if (sim_gui):
        gui_str = " --gui "
        runall_str = ""
    else:
        gui_str = ""
        if (sim_waves):
            runall_str = ""
        else:
            runall_str = " --runall --onerror quit"
    
    run_xsim_bin("xsim", snapshot + gui_str + waves_str + runall_str + " " + act_args + " --stats --log " + tests_results_path + "/sim.log")



def run_xsim_bin(name, args):
    bin_path = vivado_path + name
    #if (dbg):
    print("Call to run_xsim_bin(name='" + name + "', args='"  + args + "')")
    print("System call is " + bin_path + " " + args)
    #subprocess.call(bin_path + " " + args, shell=True)



def do_update():
    temp_path = "./tmp"
    mio_ip_base_path = pwd + "/../../../uvm_libs/mio"
    
    for root, dirs, files in os.walk(temp_path + "/mio_ip_base"):  
        for dir in dirs:
            os.chmod(path.join(root, dir), stat.S_IRWXU)
        for file in files:
            os.chmod(path.join(root, file), stat.S_IRWXU)
    
    
    # Remove old libs and temp directories
    if os.path.exists(temp_path):
        shutil.rmtree(temp_path)

    if os.path.exists(mio_ip_base_path):
        shutil.rmtree(mio_ip_base_path)
    
    if not os.path.exists(temp_path):
        os.mkdir(temp_path)
    
    # Clone repo(s) and remove extra dirs
    subprocess.call("git clone https://github.com/Datum-Technology-Corporation/mio_ip_base.git " + temp_path + "/mio_ip_base", shell=True)
    
    if os.path.exists(temp_path + "/mio_ip_base/dv/.imports"):
        shutil.rmtree(temp_path + "/mio_ip_base/dv/.imports")
    
    if os.path.exists(temp_path + "/mio_ip_base/dv/.git"):
        shutil.rmtree(temp_path + "/mio_ip_base/dv/.git")
    
    os.mkdir(mio_ip_base_path)
    
    copy_tree(temp_path + "/mio_ip_base/dv", mio_ip_base_path)
    
    
    for root, dirs, files in os.walk(temp_path + "/mio_ip_base"):  
        for dir in dirs:
            os.chmod(path.join(root, dir), stat.S_IRWXU)
        for file in files:
            os.chmod(path.join(root, file), stat.S_IRWXU)
    
    try:
        shutil.rmtree(temp_path)
    except:
        print("Failed to clean up all temporary files (" + temp_path + ")")




def copy_tree(src, dst, symlinks=False, ignore=None):
    for item in os.listdir(src):
        s = os.path.join(src, item)
        d = os.path.join(dst, item)
        if os.path.isdir(s):
            shutil.copytree(s, d, symlinks, ignore)
        else:
            shutil.copy2(s, d)
    


if __name__ == '__main__':
    args = docopt(__doc__, version='DVMake 0.1')
    if (dbg):
        print(args)
    do_dispatch(args)
