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

source "$(dirname "$0")/setup-utils.sh"

SYMFPU_DIR="${DEPS_DIR}/symfpu"

commit="8fbe139bf0071cbe0758d2f6690a546c69ff0053"

# Download and build symfpu
rm -rf "${SYMFPU_DIR}"
git clone https://github.com/martin-cs/symfpu.git "${SYMFPU_DIR}"
cd "${SYMFPU_DIR}"
git checkout $commit
git apply "${CONTRIB_DIR}/symfpu_20201114.patch"
install_include core symfpu
install_include utils symfpu
