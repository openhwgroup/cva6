Customize and Extend Generator
==============================

Add custom instructions
-----------------------

- To generate a test containing the cvxif custom instructions, run the commands below, in sim directory:
  ```bash
     cp ../env/corev-dv/custom/riscv_custom_instr_enum.sv ./dv/src/isa/custom/
     python3 cva6.py --testlist=dv/yaml/base_testlist.yaml --test riscv_arithmetic_basic_test --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=vcs-uvm
     -cs ../env/corev-dv/target/rv64gc/ --mabi lp64 --isa rv64gc --sim_opts="+uvm_set_inst_override=riscv_asm_program_gen,cva6_asm_program_gen_c,'uvm_test_top.asm_gen'" --simulator_yaml ../env/corev-dv/simulator.yaml
 ```
  The command generates the riscv_arithmetic_basic_test described in dv/yaml/base_testlist.yaml, you can define your own testlist.yaml.

- Supported targets: `rv64gc` and `rv32imc`

- CUS_EXC, CUS_M_ADD, CUS_S_ADD, CUS_NOP_EXC and CUS_ISS_EXC instructions will not be generated, because they are not yet supported by CVA6/SPIKE.

- To add new custom instructions:
   - 1. Add the new instruction enum to `riscv_custom_instr_enum.sv`
         .. code-block example:: verilog
          CUSTOM_ADD,
          CUSTOM_SUB,
          ...
   - 2. Add custom instruction definition to `rv32x_instr.sv` (or to another custom file.sv)
         .. code-block example:: verilog
          `DEFINE_CVXIF_CUSTOM_INSTR(CUSTOM_ADD, R_FORMAT, ARITHMETIC, RV32X)
          `DEFINE_CVXIF_CUSTOM_INSTR(CUSTOM_SUB, R_FORMAT, ARITHMETIC, RV32X)`
          ...
   - 3. Add your macros to `cva6_defines.svh`
         .. code-block example:
         `define DEFINE_CVXIF_CUSTOM_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
             class riscv_``instr_n``_instr extends cvxif_custom_instr;`  \
                `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)`
         ...
   - 4. If the instructions are related to cvxif: add the instr description to `cvxif_custom_instr` class
        else: Extend `riscv_custom_instr.sv` and implement key functions like get_instr_name, convert2asm
   - 5. Add RV32X to supported_isa in riscv_core_setting.sv
   - 6. Add the instruction macros to `user_define.include` or `user_define.h`

