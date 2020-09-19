#!/bin/bash

#
# Cython on Windows has some differences when compared to Linux, which ends up
# to certain expectations inside of pyboolector.pyx not being met.
#
# This file modifies pyboolector.pyx to try and avoid these -- it is not a
# patch-set because we want to avoid it being tied to a specific version of
# Boolector.
#

set -e
set -u

PYX=src/api/python/pyboolector.pyx

#
# Avoid oddities with older version of Python and math.log on a long
#
sed -i 's/math.log(a.width/math.log(int(a.width)/g' ${PYX}

#
# Avoid self.width being a long and failing a check
#
sed -i 's/upper = self.width/upper = int(self.width)/g' ${PYX}

# EOF
