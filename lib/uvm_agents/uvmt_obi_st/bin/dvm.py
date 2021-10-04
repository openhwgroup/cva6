#! /usr/bin/python3 
#######################################################################################################################
## Copyright 2021 Datum Technology Corporation
#######################################################################################################################
## SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
## Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
## with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
##                                        https://solderpad.org/licenses/SHL-2.1/
## Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
## an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
## specific language governing permissions and limitations under the License.
#######################################################################################################################


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

Options:
  -h --help     Show this screen.
  --version     Show version.
   
Examples:
  dvm.py update                                    # Download latest versions of DV libs from github
  
  dvm.py cmp  uvmt_lp_nnp                          # Only compile test bench for lp_nnp
  dvm.py elab uvmt_lp_nnp                          # Only elaborate test bench for lp_nnp
  dvm.py cpel uvmt_lp_nnp                          # Compile and elaborate test bench for lp_nnp
  dvm.py sim  uvmt_lp_nnp -t vector_playback -s 1  # Only simulates test bench for lp_nnp
  
  dvm.py all uvmt_lp_nnp -t vector_playback -s 1   # Compiles, elaborates and simulates test bench for lp_nnp
"""



from docopt     import docopt
import os
import subprocess
import shutil

dbg             = False
sim_debug       = True#False
sim_gui         = False
sim_waves       = True

pwd             = os.getcwd()
temp_path       = pwd + '/temp'
vivado_path     = '/tools/vivado/2021.1/Vivado/2021.1/bin/'
uvm_dpi_so      = "uvm_dpi"
project_dir     = pwd + "/../../../.."
rtl_path        = project_dir + "/rtl"
rtl_libs_path   = rtl_path + "/.imports"
dv_libs_path    = project_dir + "/lib/uvm_libs"
dv_agents_path  = project_dir + "/lib/uvm_agents"
dv_imports_path = project_dir + "/lib/sim_libs"


def do_dispatch(args):
    global sim_debug
    global sim_gui
    global sim_waves
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
        do_cmp_dv (dv_agents_path + "/" + args['<target>'] + "/src/" + args['<target>'] + "_pkg.flist.xsim", args['<target>'])
    if args['elab']:
        #do_elab_rtl(args['<target>'])
        do_elab(args['<target>'], args['<target>'] + "_tb")
    if args['sim']:
        do_sim(args['<target>'] + "_tb", args['<target>'] + "_" + args['<test_name>'] + "_test", args['<seed>'], [])
    if args['update']:
        do_update()


def do_paths():
    if (dbg):
        print("Call to do_paths()")
    
    ### RTL ###
    
    ### DV ###
    # Libraries
    set_env_var("UVM_HOME"                 , dv_imports_path + "/uvm"                   )
    set_env_var("DV_UVM_SRC_PATH"          , dv_imports_path + "/uvm"           + "/src")
    set_env_var("DV_UVML_SRC_PATH"         , dv_imports_path + "/uvml"          + "/src")
    set_env_var("DV_UVMA_ST_SRC_PATH"      , dv_imports_path + "/uvma_st"       + "/src")
    set_env_var("DV_UVME_ST_SRC_PATH"      , dv_imports_path + "/uvme_st"       + "/src")
    set_env_var("DV_UVMT_ST_SRC_PATH"      , dv_imports_path + "/uvmt_st"       + "/src")
    set_env_var("DV_UVML_LOGS_SRC_PATH"    , dv_imports_path + "/uvml_logs"     + "/src")
    set_env_var("DV_UVML_SB_SRC_PATH"      , dv_imports_path + "/uvml_sb"       + "/src")
    set_env_var("DV_UVML_RAL_SRC_PATH"     , dv_imports_path + "/uvml_ral"      + "/src")
    set_env_var("DV_UVMA_RESET_SRC_PATH"   , dv_imports_path + "/uvma_reset"    + "/src")
    set_env_var("DV_UVME_RESET_ST_SRC_PATH", dv_imports_path + "/uvme_reset_st" + "/src")
    set_env_var("DV_UVMT_RESET_ST_SRC_PATH", dv_imports_path + "/uvmt_reset_st" + "/src")
    set_env_var("DV_UVMA_CLK_SRC_PATH"     , dv_imports_path + "/uvma_clk"      + "/src")
    set_env_var("DV_UVME_CLK_ST_SRC_PATH"  , dv_imports_path + "/uvme_clk_st"   + "/src")
    set_env_var("DV_UVMT_CLK_ST_SRC_PATH"  , dv_imports_path + "/uvmt_clk_st"   + "/src")
    
    # Source
    set_env_var("DV_UVML_MEM_SRC_PATH"   , dv_libs_path   + "/uvml_mem"    + "/src")
    set_env_var("DV_UVMA_OBI_SRC_PATH"   , dv_agents_path + "/uvma_obi"    + "/src")
    set_env_var("DV_UVME_OBI_ST_SRC_PATH", dv_agents_path + "/uvme_obi_st" + "/src")
    set_env_var("DV_UVMT_OBI_ST_SRC_PATH", dv_agents_path + "/uvmt_obi_st" + "/src")


def set_env_var(name, value):
    if (dbg):
        print("Setting env var '" + name + "' to value '" + value + "'")
    os.environ[name] = value


def do_clean():
    if (dbg):
        print("Call to do_clean()")
    print("\033[1;31m********")
    print("Cleaning")
    print("********\033[0m")
    if os.path.exists("./xsim.dir"):
        shutil.rmtree("./xsim.dir")
    if os.path.exists("./out"):
        shutil.rmtree("./out")


def do_cmp_rtl(target_design):
    if (dbg):
        print("Call to do_cmp_rtl(target_design='" + target_design + "'")
    


def do_cmp_dv(filelist_path, lib_name):
    if (dbg):
        print("Call to do_cmp_dv(filelist_path='" + filelist_path + "', lib_name='" + lib_name + "')")
    print("\033[0;36m************")
    print("Compiling DV")
    print("************\033[0m")
    
    run_xsim_bin("xvlog", "--incr -sv -f " + filelist_path + " -L uvm --work " + lib_name + "=./out/" + lib_name + " --log ./out/compilation.log")


def do_elab(lib_name, design_unit):
    
    debug_str = ""

    if (dbg):
        print("Call to do_elab(lib_name='" + lib_name + "', design_unit='" + design_unit + "')")
    print("\033[0;36m***********")
    print("Elaborating")
    print("***********\033[0m")
    
    if (sim_debug):
        debug_str = " --debug all "
    else:
        debug_str = ""

    run_xsim_bin("xelab", lib_name + "." + design_unit + debug_str + " --incr -relax --O0 -v 0 -s " + design_unit + " -timescale 1ns/1ps -L " + lib_name + "=./out/" + lib_name + " --log ./out/elaboration.log")
    


def do_sim(snapshot, test_name, seed, args):
    
    waves_str = ""
    gui_str   = ""
    runall_str   = ""
    
    tests_results_path = pwd + "/results/" + test_name + "_" + str(seed)
    
    args.append("SIM_DIR_RESULTS="                 + pwd + "/results")
    args.append("UVM_TESTNAME="                    + test_name + "_c")
    args.append("UVML_FILE_BASE_DIR_SIM="          + pwd)
    args.append("UVML_FILE_BASE_DIR_TB="           + dv_path  + "/" + snapshot + "/src")
    args.append("UVML_FILE_BASE_DIR_TESTS="        + dv_path  + "/" + snapshot + "/src/tests")
    args.append("UVML_FILE_BASE_DIR_TEST_RESULTS=" + tests_results_path)
    args.append("UVML_FILE_BASE_DIR_DV="           + dv_path)
    args.append("UVML_FILE_BASE_DIR_RTL="          + rtl_path)

    act_args = ""
    for arg in args:
        act_args = act_args + " -testplusarg \"" + arg + "\""
    
    if not os.path.exists(tests_results_path):
        os.mkdir(tests_results_path)
    if not os.path.exists(tests_results_path + "/trn_log"):
        os.mkdir(tests_results_path + "/trn_log")
    
    if (dbg):
        print("Call to do_sim(snapshot='" + snapshot + "', test_name='" + test_name + "', seed='" + str(seed) + "', args='" + act_args + "')")
    
    print("\033[0;32m**********")
    print("Simulating")
    print("**********\033[0m")
    
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


def do_update():
    if not os.path.exists(dv_imports_path):
        shutil.rmtree(dv_imports_path)
    clone_repo_dv_to_imports("https://github.com/Datum-Technology-Corporation/mio_ip_core.git", "uvml_sb"  , "uvml_sb"  )
    clone_repo_dv_to_imports("https://github.com/Datum-Technology-Corporation/mio_ip_core.git", "uvml"     , "uvml"     )
    clone_repo_dv_to_imports("https://github.com/Datum-Technology-Corporation/mio_ip_core.git", "uvml_logs", "uvml_logs")


def clone_repo_dv_to_imports(uri, branch, dv_ip_name):
    dst_path = dv_imports_path + "/" + dv_ip_name
    
    if not os.path.exists(dv_imports_path):
        os.mkdir(dv_imports_path)
    if os.path.exists(temp_path):
        shutil.rmtree(temp_path)
    if os.path.exists(dst_path):
        shutil.rmtree(dst_path)
    else:
        os.mkdir(dst_path)
    print("Cloning " + uri + " branch " + branch + " for " + dv_ip_name)
    subprocess.call("git clone -q --branch " + branch + " " + uri + " " + temp_path, shell=True)
    copy_tree(temp_path + "/dv/" + dv_ip_name, dst_path)
    shutil.rmtree(temp_path)


def copy_tree(src, dst, symlinks=False, ignore=None):
    for item in os.listdir(src):
        s = os.path.join(src, item)
        d = os.path.join(dst, item)
        if os.path.isdir(s):
            shutil.copytree(s, d, symlinks, ignore)
        else:
            shutil.copy2(s, d)


def run_xsim_bin(name, args):
    bin_path = vivado_path + name
    if (dbg):
        print("Call to run_xsim_bin(name='" + name + "', args='"  + args + "')")
        print("System call is " + bin_path + " " + args)
    subprocess.call(bin_path + " " + args, shell=True)


if __name__ == '__main__':
    args = docopt(__doc__, version='DVMake 0.1')
    if (dbg):
        print(args)
    do_dispatch(args)

