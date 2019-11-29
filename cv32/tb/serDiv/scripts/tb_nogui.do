vsim -t ps \
     tb

#turn off disturbing warnings...
set StdArithNoWarnings 1
set StdNumNoWarnings 1
set NumericStdNoWarnings 1

run -all
exit -f

