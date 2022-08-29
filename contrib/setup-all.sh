#!/usr/bin/env bash
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

set -e -o pipefail

./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh
./contrib/setup-cms.sh
./contrib/setup-kissat.sh
./contrib/setup-gimsatul.sh
./contrib/setup-lingeling.sh
./contrib/setup-symfpu.sh
