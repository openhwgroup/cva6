# BRAM Data Width Converter Behavioral Testbench

## Running Tests

This module depends on the `CfMath` package.  You have to specify the path to this package when
running tests.  If this module is not used as part of the `big.pulp` project, specify the correct
path to the package in `CF_MATH_PKG_PATH`, e.g.,

    CF_MATH_PKG_PATH=../../../../../fe/ips/pkg/cfmath make
