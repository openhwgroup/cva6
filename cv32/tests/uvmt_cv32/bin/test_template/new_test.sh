#!/bin/bash

sed -i -E "s/\$\{name\}/${1}/" test_template.sv > uvmt_cv32_${1}_test.sv
