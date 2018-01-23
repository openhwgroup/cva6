#!/bin/sh
set -e
cd "$(dirname "${BASH_SOURCE[0]}")/.."
[ -d tmp ] || ln -s "$(mktemp -d -t ariane.XXXXXXXX)" tmp
