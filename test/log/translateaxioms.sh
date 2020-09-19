#!/bin/sh
for i in 1 2 3 4 5 6 7 8 16 32 64
do
  for axiom in *.axiom
  do
    name=smtaxiom`basename $axiom .axiom`$i.smt
    echo $name
    rm -f $name
    ./translateaxiom.sh $axiom $i > $name
  done
done
