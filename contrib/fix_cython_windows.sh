#!/bin/bash
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##
#
# Cython on Windows has some differences when compared to Linux, which ends up
# to certain expectations inside of pybitwuzla.pyx not being met.
#
# This file modifies pybitwuzla.pyx to try and avoid these -- it is not a
# patch-set because we want to avoid it being tied to a specific version of
# Bitwuzla.
#

set -e
set -u

PYX=src/api/python/pybitwuzla.pyx

#
# Avoid oddities with older version of Python and math.log on a long
#
sed -i 's/math.log(a.width/math.log(int(a.width)/g' ${PYX}

#
# Avoid self.width being a long and failing a check
#
sed -i 's/upper = self.width/upper = int(self.width)/g' ${PYX}

# EOF
