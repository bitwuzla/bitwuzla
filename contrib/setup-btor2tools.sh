#!/usr/bin/env bash
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

BTOR2TOOLS_DIR="${DEPS_DIR}/btor2tools"
COMMIT_ID="6ba194b3d58774b5d13e92b198367dedd5b80236"

download_github "boolector/btor2tools" "$COMMIT_ID" "$BTOR2TOOLS_DIR"
cd "${BTOR2TOOLS_DIR}"

if is_windows; then
  component="Btor2Tools"
  last_patch_date="20190110"
  test_apply_patch "${component}" "${last_patch_date}"
fi

mkdir build
cd build
cmake .. \
  -DBUILD_SHARED_LIBS=OFF \
  -DCMAKE_INSTALL_PREFIX=${INSTALL_DIR} \
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON
make install -j${NPROC}
