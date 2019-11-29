#vsim -sva -assertdebug -t ps tb
vsim -voptargs="+acc" -t ps tb

#turn off disturbing warnings...
#set NumericStdNoWarnings  1

do wave.do
run -all
