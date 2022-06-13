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
COMMIT_ID="sc2021"

rm -rf "${KISSAT_DIR}"

# Download and build Kissat
TAR_ARGS=""
download_github "arminbiere/kissat" "$COMMIT_ID" "$KISSAT_DIR" "$TAR_ARGS"
cd "${KISSAT_DIR}"

./configure -fPIC --quiet ${EXTRA_FLAGS}
make -j${NPROC}
install_lib build/libkissat.a
install_include src/kissat.h

