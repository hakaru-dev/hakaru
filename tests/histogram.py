#!/usr/bin/python

# Histogram plotting tool to check the shape of distributions
# Justin Staples
# October 16th, 2017

# Usage: python histogram.py test.hk N
# Where test.hk is the hakaru program that generates a stream of samples 
# from the distribution and N is the number of samples. Raw output is written
# to the file "results.txt". These strings are converted to floating point
# numbers and then written to the file "samples.txt". 

import os
import sys
import matplotlib.pyplot as plt

filename = sys.argv[1]
nos = sys.argv[2]

command = "hakaru -w " + filename + " | head -n " + nos + " > results.txt"
print(command)

os.system(command)

data = open("results.txt", "r")

samples = []

for i in range(int(nos)):
	line = data.readline()
	sample = float(line)
	#if (sample >=0 and sample <=4):
	samples.append(sample)

plt.hist(samples, 100)
plt.show()

res = open("samples.txt", "w")

for sample in samples:
  res.write("%s\n" % sample)

