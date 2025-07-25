#!/bin/bash

exit_error() {
    echo "$1" >&2
    exit ${2:-1}
}

if [ "$#" -ne 1 ]; then
    exit_error "Usage: $0 <executable>" 2
fi

exe="$1"
base=$(basename "$exe" .o)

#TODO 