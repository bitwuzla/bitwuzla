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

source "$(dirname "$0")/setup-utils.sh"

KISSAT_DIR="${DEPS_DIR}/kissat"

rm -rf "${KISSAT_DIR}"

# Download and build Kissat Extras
download_github jix/kissat_extras main "${KISSAT_DIR}"
cd "${KISSAT_DIR}"

./configure -fPIC ${EXTRA_FLAGS}
make -j${NPROC}
install_lib build/libkissat.a
install_include src/kissat.h

if grep -q 'dev' VERSION; then
  echo
  echo "This is a development snapshot of Kissat Extras and might not be ready for production use."
  echo
fi
