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

GIMSATUL_DIR="${DEPS_DIR}/gimsatul"
COMMIT_ID="rel-1.0.1"

TAR_ARGS=""
if is_windows; then
  # Extracting a symlink to a non-existing file fails on Windows, so we exclude it
  TAR_ARGS="--exclude src/makefile"
fi

download_github "arminbiere/gimsatul" "$COMMIT_ID" "$GIMSATUL_DIR" "$TAR_ARGS"
cp contrib/Gimsatul.cmake "${GIMSATUL_DIR}/CMakeLists.txt"
cd "${GIMSATUL_DIR}"

echo "#define COMPILER \"@CMAKE_C_COMPILER_ID@ @CMAKE_C_COMPILER_VERSION@ @CMAKE_C_FLAGS@\"
#define GITID \"\"
#define VERSION \"1.0.1\"
#define BUILD \"@CMAKE_SYSTEM_NAME@ @CMAKE_SYSTEM_VERSION@\"" > config.h.in
mkdir -p build
cd build
cmake .. -DCMAKE_INSTALL_PREFIX="${INSTALL_DIR}"
make install -j${NPROC}
