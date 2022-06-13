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

CADICAL_DIR="${DEPS_DIR}/cadical"
COMMIT_ID="rel-1.5.2"

TAR_ARGS=""
if is_windows; then
  # Extracting a symlink to a non-existing file fails on Windows, so we exclude it
  TAR_ARGS="--exclude src/makefile"
fi

download_github "arminbiere/cadical" "$COMMIT_ID" "$CADICAL_DIR" "$TAR_ARGS"
cd "${CADICAL_DIR}"

if is_windows; then
  component="CaDiCaL"
  last_patch_date="20190730"
  test_apply_patch "${component}" "${last_patch_date}"
  EXTRA_FLAGS="-q"
  #
  # CaDiCaL performs configure checks with -Werror, which fails on Windows as
  # fPIC is not valid, so we set CXXFLAGS per-platform
  #
  export CXXFLAGS=""
else
  export CXXFLAGS="-fPIC"
fi

./configure ${EXTRA_FLAGS}
make -j${NPROC}
install_lib build/libcadical.a
install_include src/ccadical.h
