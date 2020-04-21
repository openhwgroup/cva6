#!/usr/bin/env python3
#
# This is free and unencumbered software released into the public domain.
#
# Anyone is free to copy, modify, publish, use, compile, sell, or
# distribute this software, either in source code form or as a compiled
# binary, for any purpose, commercial or non-commercial, and by any
# means.

from sys import argv

binfile = argv[1]
nwords = int(argv[2])
dumptype = argv[3]

with open(binfile, "rb") as f:
    bindata = f.read()

# TODO: make better assertions
# assert len(bindata) < 4*nwords
# assert len(bindata) % 4 == 0 # not necessarily true if we have data

if dumptype == "word":
    for i in range(nwords):
        if i < len(bindata) // 4:
            w = bindata[4*i : 4*i+4]
            print("%02x%02x%02x%02x" % (w[3], w[2], w[1], w[0]))
        else:
            print("0")
elif dumptype == "bin":
    for i in range(nwords):
        if i < len(bindata):
            w = bindata[i]
            print("%02x" % (w))
        else:
            print("0")

else:
    print("prove a dump format argument")
