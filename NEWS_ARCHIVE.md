### NEWS UPDATES (going back to early 2020):
**2020-12-10**: OpenHW formally decalres [RTL Freeze for CV32E40P](https://www.openhwgroup.org/news/2020/12/10/core-v-cve4-rtl-freeze-milestone-achieved/)
<br>
**2020-10-15**: Aldec's Riviera-PRO SystemVerilog simulator is now supported by core-v-verif.  Check out the README in [mk/uvmt](https://github.com/openhwgroup/core-v-verif/tree/master/mk/uvmt#running-the-environment-with-aldec-riviera-pro-riviera) for more information.
<br>
**2020-09-04**: a new (and _much_ better) method of specifying and organizating test-programs and simulations is now merged in.  See slide "_Test Specification Updates_" in the [2020-08-31 CV32E40P project update](https://github.com/openhwgroup/core-v-docs/blob/master/verif/MeetingPresentations/20200831-CV32E40P-ProjectScheduleUpdate.pptx).
<br>
**2020-06-12**: a new "Board Support Package" for CV32E40P simulations is installed at `cv32/bsp`.  This BSP should be used to compile/assemble your [test-programs](https://core-v-docs-verif-strat.readthedocs.io/en/latest/test_program_environment.html).  The Makefiles for both the CORE testbench and UVM verification environment have been updated to use this BSP.
<br>
**2020-06-02:** The [Imperas OVPsim Instruction Set Generator](http://www.ovpworld.org/) has been integrated into the UVM environment as the Referenece Model for the CV32E40(P).  You will need to obtain a license from Imperas to use it.
<br>
**2020-02-28:** The OpenHW Group CV32E40P is now live!<br>This repository no longer contains a local copy of the RTL.  The RTL is cloned from the appropriate [core-v-cores](https://github.com/openhwgroup/core-v-cores) repository as needed.  The specific branch and hash of the RTL is controlled by a set of variables in `cv32e40p/sim/Common.mk`.
<br>
**2020-02-10:** The core-v-verif repository now supports multiple cores.  The previously named cv32 directory is now cv32e40p to represent the testbench for the CV32E40P core.  Future cores will be verified in respectively named directories in core-v-verif as siblings to cva6 and cv32e40p.

