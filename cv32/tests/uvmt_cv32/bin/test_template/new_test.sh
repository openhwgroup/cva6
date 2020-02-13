#!/bin/bash

test_name=$1
test_name_uppercase=${test_name^^}
cat test_template.sv | sed -E "s/[$][{]name_uppercase[}]/$test_name_uppercase/g" | sed -E "s/[$][{]name[}]/$test_name/g" > uvmt_cv32_${test_name}_test.sv
