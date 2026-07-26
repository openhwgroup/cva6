#Cook
export CONFIG_DIR=/config_cook_path/cook #shared config directory (techno.yml compile.yml setenv.sh)
#Spike
export SPIKE_PATH=/spike_path/spike #shared root directory of spike installation
export NUM_JOBS=24
#Synopsys
export SYN_VCS_BASHRC=/synopsys_path/vcs/version/setup/bashrc.example
export SYN_VERDI_BASHRC=/synopsys_path/verdi/version/setup/bashrc.example
export VCS_UVM_HOME=/synopsys_path/vcs/version/etc/uvm-1.2/
export SYN_SG_BASHRC=/synopsys_path/spyglass/version/setup/bashrc.example
export SYN_DCSHELL_BASHRC=/synopsys_path/syn/version/setup/bashrc.example
#Cadence
export CADENCE_XCELIUM_BASHRC=/cadence_path/xcelium/version/setup/bashrc.example
export XCELIUM_HOME=/cadence_path/xcelium/version  # Required for UVM paths
#Siemens (Mentor)
export SIEMENS_QUESTA_BASHRC=/siemens_path/questa/version/setup/bashrc.example
#export QUESTASIM_HOME=/siemens_path/questa/version  # Optional: auto-detected from vsim
#Generic tool
export VERIBLE_PATH=/verible_path/verible-v0.0-3922-g26d4b0e0/bin
#Python Black/pylint
export PYTHON_PATH=~/.local/bin
#Report to dashboard CI
export DASHBOARD_USER_EMAIL=gituser@example.com
export DASHBOARD_USER_NAME="gituser"
export DASHBOARD_URL="git@exemple.com:group/dashboard.git"
#Update Path
export PATH=$PATH:$VERIBLE_PATH
export PATH=$PATH:$PYTHON_PATH

#source $SYN_VERDI_BASHRC
#source $SYN_VCS_BASHRC
#source $SYN_SG_BASHRC
#source $SYN_DCSHELL_BASHRC
#source $SYN_PTSHELL_BASHRC
#source $CADENCE_XCELIUM_BASHRC
#source $SIEMENS_QUESTA_BASHRC
