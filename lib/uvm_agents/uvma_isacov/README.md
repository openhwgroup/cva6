This UVM agent is for ISA coverage.
It has support for IMCZifencei_Zicsr and can be extended to support other extensions.
As a passive agent, its monitor is fed retired instructions which are then decoded and fed to the coverage model.

To enable use of the required disassembler's shared object file, the following environment variables must be set:
`XRUN_ELAB_COV_FLAGS='+define+DPI_DASM'`,
`XRUN_RUN_COV_FLAGS='-sv_lib $(DPI_DASM_PKG)/libdpi_dasm.so'`.
See `lib/dpi_dasm/README.md` for more details.
TODO this should be automatic with COV=1 via XRUN_ELAB_COV and XRUN_RUN_COV when uvma_isacov is complete (WIP),
and "+define+COV" should be used instead of "+define+DPI_DASM".
