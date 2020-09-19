#!/bin/bash

source "$(dirname "$0")/setup-utils.sh"

CMS_DIR=${DEPS_DIR}/cryptominisat

download_github "msoos/cryptominisat" "5.6.3" "$CMS_DIR"
cd ${CMS_DIR}

mkdir build
cd build
cmake -DENABLE_PYTHON_INTERFACE=OFF \
      -DSTATICCOMPILE=ON \
      -DNOM4RI=ON \
      -DONLY_SIMPLE=ON \
      -DCMAKE_INSTALL_PREFIX="${INSTALL_DIR}" \
      ..
make libcryptominisat5 -j${NPROC} install
