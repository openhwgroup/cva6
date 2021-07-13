## Xcelium tools directory

Various Xcelium-based utilities and scripts.

### Simulator control scripts

These TCL scripts can be passed to Xcelium by the core-v-verif Makefiles when using Xcelium.  The following scripts are currently supported:

| Script | Usage |
|--------|-------|
| probe.tcl | Generates probes for waveform database viewable with Cadence SimVision.  Invoked when WAVES=1 passed to the make test command |
| indago.tcl | Generates probes for waveform database viewable with Cadence Indago.  Invokedf when WAVEs=1 ADV_DEBUG=1 passed to the make test command |

### Coverage refinement files

These XML files should be created using coverage tools such as IMC or Vmanager.  These are used to generate coverage reports that focus on necessary coverage while removing exceptions that are unhittable or not significant for the design being verified.

*Note that some files are automatically generated and some are manually maintained.  This is indicated in the table.*

| File | Maintenance | Description |
|------|-------------|-------------|
| cv32e40s.hierarchy.vRefine | Manual | Removes hierarchies from coverage database that are not to be considered for coverage (e.g. testbench |
| cv32e40s.auto.vRefine | Automatic | Auto-generated refinements based on parameter usage for the CV32E40S without PULP extensions.  *Do not manually edit* |
| cv32e40s.manual.vRefine | Manual | Manually added coverage exception based on deesign verification reviews. |
