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

source "$(dirname "$0")/setup-utils.sh"

CMS_DIR="${DEPS_DIR}/cryptominisat"

download_github "msoos/cryptominisat" "5.7.0" "$CMS_DIR"
cd "${CMS_DIR}"

mkdir build
cd build
cmake -DENABLE_PYTHON_INTERFACE=OFF \
      -DSTATICCOMPILE=ON \
      -DNOM4RI=ON \
      -DONLY_SIMPLE=ON \
      -DCMAKE_INSTALL_PREFIX="${INSTALL_DIR}" \
      ..
make -j${NPROC} install
