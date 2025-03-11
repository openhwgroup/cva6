# Make sure to source this script from the root directory 
# to correctly set the environment variables related to the tools
source ./verif/sim/setup-env.sh
DV_TARGET=cv64a6_imafdc_sv39

# Set the NUM_JOBS variable to increase the number of parallel make jobs
# export NUM_JOBS=

export DV_SIMULATORS=veri-testharness
#export DV_SIMULATORS=spike
export TRACE_FAST=1

cd ./verif/sim

# sv39 is structure of the virtual memory
# core/include i can change the configuration
python3 -c "
from cva6 import generate_fpga_files
# Define parameters
c_test = '../../ad_tests/TVLA-tests/uart_trigger_aes/uart_trigger_aes.c'
linker = '../tests/custom/common/test.ld'
gcc_opts = '-static -mcmodel=medany -fvisibility=hidden -O0 -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -lgcc -I../tests/custom/env -I../tests/custom/common'
output_dir = './FPGA_output'
isa = 'rv64imafdc'
mabi = 'lp64'
# Call the function
generate_fpga_files(c_test=c_test, linker=linker, gcc_opts=gcc_opts, isa=isa, mabi=mabi, output_dir=output_dir)
"

cd ..
cd ..