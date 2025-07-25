# Author:  Umberto Laghi
# Contact: umberto.laghi2@unibo.it
# Github:  @ubolakes

clean:
	rm -rf transcript
	rm -rf encapsulator.mpf
	rm -rf encapsulator.cr.mti
	rm -rf modelsim.ini
	rm -rf work
	rm -rf vsim.wlf
	rm -rf addfiles.do
	rm -rf .bender
	rm -rf Bender.lock

run:
	bender update
	python3 generate_do.py
	questa-2022.3 vsim -do addfiles.do
