VER                 = 2016.1
VIVADO_SOURCE_CMDS  = -source scripts/setup.tcl -source scripts/synthesize.tcl

CF_MATH_PKG_PATH	= ../../../../ips/pkg/cfmath

nogui: pkgdeps synth_nogui

gui: pkgdeps synth_gui

pkgdeps:
	@if [ ! -e $(CF_MATH_PKG_PATH)/CfMath.sv ]; then \
		echo "Error: Dependency 'CfMath.sv' not found, please specify 'CF_MATH_PKG_PATH'!"; \
		exit 1; \
	fi; \
	ln -t deps/ -sf ../$(CF_MATH_PKG_PATH)/CfMath.sv

synth_nogui:
	@vivado-${VER} vivado -mode batch $(VIVADO_SOURCE_CMDS)

synth_gui:
	@vivado-${VER} vivado -mode gui $(VIVADO_SOURCE_CMDS)

clean:
	@rm -f *.jou *.log vivado_*.str
	@rm -rf vivado.*

