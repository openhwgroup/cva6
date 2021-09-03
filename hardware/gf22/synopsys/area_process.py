#!/usr/bin/python3

import numpy as np
import os
import os.path
import argparse
import sys
import matplotlib.pyplot as plt

parser = argparse.ArgumentParser(description='Generate hyper memory image file from slm')

parser.add_argument("--input", dest="input_file", default=None, help="Specify input file (ex. ./area.rpt)")

parser.add_argument("--hier", dest="hier", default=0, help="Specify input file (ex. ./area.rpt)")

parser.add_argument("--filter", dest="filter", default=10, help="Specify minimum % to appear in the bar")

args = parser.parse_args()

if args.input_file is None:
    raise Exception('Specify the input file with --input=<path> (ex. --input=./area.rpt)')

if args.hier is None:
    raise Exception('Specify the hierarchical level you are interested in with --hier N')

if args.hier is None:
    raise Exception('Specify the minimum percentage for a design block to appear with --filter n')

delimiter=" "
with open(args.input_file, "rU") as fi:
    data = list(map(lambda x:x.split(), fi.read().strip().split("\n")))

A=np.array(data)
B=np.array([])
j=0
mystrings=A[:,0]

## filter list skipping first element (alsaqr)
for i in range (1,A.shape[0]):
   if mystrings[i].count("/") == int(args.hier):
      B=np.append(B,np.array(A[i]),axis=0)
      j=j+1

B=np.reshape(B,(j,A.shape[1]))

temp=B[:,1]
temp=temp.astype(float)
sum_B=temp.sum()
filtered_B=np.array([])

## plot what matters
r=0
for i in range (0,B.shape[0]):
   if temp[i]*100/sum_B>float(args.filter):
      filtered_B=np.append(filtered_B,np.array(B[i]),axis=0)
      r=r+1

filtered_B=np.reshape(filtered_B,(r,B.shape[1]))
x_tick_labels=filtered_B[:,0]
C=filtered_B[:,1]
   
from random import randint
colors = []
for i in x_tick_labels:
    colors.append('#%06X' % randint(0, 0xFFFFFF))
    
fig1, ax1 = plt.subplots()

width=0.25
x=np.arange(len(x_tick_labels))

C=C.astype(float)


percentages=C*100/sum_B

ax1.set_xticklabels(x_tick_labels, rotation='horizontal', fontsize=7)

ax1.bar(x_tick_labels,percentages,width,color=colors)
plt.title("Total area: "+A[0][1]+"$\mu m^2$\nHierarchical level:"+args.hier+"\nShowing components with area >"+args.filter+"%")
plt.ylabel("area %")
plt.show()
