#!/bin/bash

vlib ./work

vlog -sv               ../../../alu_div.sv  || exit 1
vlog -sv +incdir+../   ../tb.sv             || exit 1
