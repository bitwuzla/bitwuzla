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

MINISAT_DIR="${DEPS_DIR}/minisat"
COMMIT_ID="37dc6c67e2af26379d88ce349eb9c4c6160e8543"

download_github "niklasso/minisat" "$COMMIT_ID" "$MINISAT_DIR"
cd "${MINISAT_DIR}"

make config prefix="${INSTALL_DIR}" -j${NPROC}
make install
