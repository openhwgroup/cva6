bender script vsim --target="test" --vlog-arg="+cover=bcfst+/dut -64 -nologo -suppress 13262,2583 -permissive -pedanticerrors -svinputport=compat" --vcom-arg="-64 -nologo -2008" > ./scripts/compile_vsim_bender.tcl
#-svinputport=compat -quiet
