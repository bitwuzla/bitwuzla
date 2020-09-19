#!/bin/sh
msb="`expr $2 - 1`"
echo "(benchmark smtaxiom`basename $1 .axiom`"
echo " :logic QF_BV"
echo " :extrafuns ((s BitVec[$2]))"
echo " :extrafuns ((t BitVec[$2]))"
echo " :formula (not (="
sed -e 's/abbreviates//g' -e "s,|m-1|,$msb,g" $1
echo ")))"
