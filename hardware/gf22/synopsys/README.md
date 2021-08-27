# Synth flow

Basic list of commands to perform synthesis. From the hardware folder.

```
make scripts-bender-synopsys

```
This will generate the `<tech>/synopsys/scripts/analyze_alsaqr.tcl` file we need to pass to the synth tool.

From the synopsys folder:
```
synopsys dc_shell-xg-t -64 -topo -f ./scripts/go_synth.tcl alsqr.tcl

```

## Tips

There are several technology dependet cells we need to check out before launching the synthesis.

 - The memories:
       * tc_sram in l2_subsystem
       * tc_sram in the cache subsystem
       * generic memories in the cluster
 - The pads
 - Delay lines for the hyper

You can instantiate your macros as wrapped in the tc_sram and pad files according to the `Bender.yml`.
Support for generic memories and delay lines is still missing.