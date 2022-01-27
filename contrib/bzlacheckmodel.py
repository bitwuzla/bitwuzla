#!/usr/bin/env python
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

import sys, os, random, signal

def dec2bin(dec, len):
  binary = bin(dec).split('b')[1]
  evalstring= "%0" + str(len) + "d"
  return evalstring % int(binary)

if len(sys.argv) != 4:
  print("Usage: ./bzlacheckmodel <bzla-file> <bzla-output-model-file> <bitwuzla-binary>")
  sys.exit(2)

pid = os.getpid();
foutname = "/tmp/bzlacheckmodel" + str(pid) +".btor"
# get absolute path to bitwuzla binary
bitwuzla = sys.argv[3]


def cleanup():
  try:
    os.remove(foutname)
  except:
    pass # ignore exception

def signalhandler(signum, frame):
  cleanup()
  sys.exit(0)

signal.signal(signal.SIGINT, signalhandler)
signal.signal(signal.SIGTERM, signalhandler)
signal.signal(signal.SIGHUP, signalhandler)
fout = open (foutname, "w")
arrays = {} 
arrayass = {}
constants = {}
foundroot=False
with open (sys.argv[1], "r") as fin:
  for origline in fin:
    line = origline.strip()
    words = line.split()

    if words[1] == "root":
      if foundroot:
        print("Multiple roots are not supported")
        sys.exit(2)
      foundroot=True
      id = int(words[0])
      rootarg = words[3]
    else:
      if words[1] == "array":
        if int(words[3]) > 8:
          print("Arrays with index len > 8 are not supported")
          sys.exit(2)
        arrays[words[0]]=words[2] + " " + words[3]
        arrayass[words[0]]={}
        if words[2] not in constants:
          randnr = random.randint(0, (2 ** int(words[2])) - 1)
          constants[words[2]]=dec2bin (randnr, int(words[2]))
      fout.write (origline) 

if foundroot == False:
  print("Root is missing")
  sys.exit(2)

fout.write (str(id) + " const 1 1\n")
lastand = id
id = id + 1

with open (sys.argv[2], "r") as fin:
  origline = fin.readline()
  if origline.strip() != "sat":
      print("Formula is not SAT")
      sys.exit(2)
  for origline in fin:
    line = origline.strip()
    words = line.split()
    opos = words[0].find("[")
    if opos == -1:
      #bv model
      modelid= words[0]
      #check if modelid is really an integer or an identifier
      try:
        temp = int(modelid)
      except:
        print("invalid identifier")
        sys.exit(2)
        ## modelid is an identifier, we have to get the id
        #ret = os.popen ("grep \"\<" + modelid + "\>\" " + sys.argv[1] + \
        #                "| awk '{print $1}'")
        #lines = ret.readlines()
        #if len(lines) > 1:
        #  print "BV identifier is not unique"
        #  sys.exit(1)
        #if len(lines) == 0:
        #  print "Cannot find BV identifier"
        #  sys.exit(1)
        #modelid = lines[0].strip()

      ass = words[1]
      assl = len(ass)
      randnr = random.randint (0, 1)
      ass = ass.replace("x", str(randnr))
      fout.write (str(id) + " const " + str(assl) + " " + ass + "\n")
      lastid = str(id)
      id = id + 1
      fout.write (str(id) + " eq 1 " + modelid + " " + lastid + "\n")
      lastid = str(id)
      id = id + 1
      fout.write (str(id) + " and 1 " + str(lastand) + " " + lastid + "\n")
      lastand = id
      id = id + 1
    else:
      cpos = words[0].find("]")

      if cpos == -1:
        print("Invalid format of model file")
        sys.exit(2)

      aid=line[0:opos]
      #check if array id is really an integer or an identifier
      try:
        temp = int(aid)
      except:
        print("invalid identifier")
        sys.exit(2)
        ## aid is an identifier, we have to get the id
        #ret = os.popen ("grep \"\<" + aid + "\>\" " + sys.argv[1] + \
        #                "| awk '{print $1}'")
        #lines = ret.readlines()
        #if len(lines) > 1:
        #  print "Array identifier is not unique"
        #  sys.exit(1)
        #if len(lines) == 0:
        #  print "Cannot find array identifier"
        #  sys.exit(1)
        #aid = lines[0].strip()

      iass=line[opos + 1:cpos]
      iassl=len(iass)
      if iass.find("x") != -1:
        print("Unexpected index assignment")
        sys.exit(2)

      vass=words[1]
      vassl=len(vass)
      if vass.find("x") != -1:
        print("Unexpected value assignment")
        sys.exit(2)
      
      fout.write(str(id) + " const " + str(iassl) + " " + iass + "\n")
      iid = lastid = str(id)
      id = id + 1
      fout.write(str(id) + " const " + str(vassl) + " " + vass + "\n")
      vid = lastid = str(id)
      id = id + 1
      fout.write(str(id) + " read " + str(vassl) + " " + aid + " " + iid + "\n")
      lastid = str(id)
      id = id + 1
      fout.write(str(id) + " eq 1 " + vid + " " + lastid + "\n")
      lastid = str(id)
      id = id + 1
      fout.write (str(id) + " and 1 " + str(lastand) + " " + lastid + "\n")
      lastand = id
      id = id + 1

      # remember assignment
      arrayass[aid][iass] = vass

for key in arrays:
  words = arrays[key].split()
  vlen = words[0]
  ilen = words[1]
  looprange = range (0, 2 ** int(ilen))
  ass = arrayass[key]
  constant = constants[vlen]
  for i in looprange:
    binary = dec2bin (i, ilen)
    if binary not in ass:
      fout.write(str(id) + " const " + str(ilen) + " " + binary + "\n")
      iid = lastid = str(id)
      id = id + 1
      fout.write(str(id) + " const " + str(vlen) + " " + constant + "\n")
      vid = lastid = str(id)
      id = id + 1
      fout.write(str(id) + " read " + str(vlen) + " " + key + " " + iid + "\n")
      lastid = str(id)
      id = id + 1
      fout.write(str(id) + " eq 1 " + vid + " " + lastid + "\n")
      lastid = str(id)
      id = id + 1
      fout.write (str(id) + " and 1 " + str(lastand) + " " + lastid + "\n")
      lastand = id
      id = id + 1

fout.write(str(id) + " implies 1 " + str(lastand) + " " + rootarg + "\n")
lastid = id
id = id + 1
fout.write(str(id) + " root 1 -" + str(lastid) + "\n")
fout.close()

ret = os.popen (bitwuzla + " -rwl 0 " + foutname)
result = ret.readline().strip()
if result == "sat":
  print("Invalid")
  sys.exit(1)
elif result != "unsat":
  print("Unexpected result")
  sys.exit(2)

cleanup()
print("Valid")
sys.exit(0)
