#!/usr/bin/env bash

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

MINISAT_DIR=${DEPS_DIR}/minisat
COMMIT_ID="37dc6c67e2af26379d88ce349eb9c4c6160e8543"

download_github "niklasso/minisat" "$COMMIT_ID" "$MINISAT_DIR"
cd ${MINISAT_DIR}

make config prefix=${INSTALL_DIR} -j${NPROC}
make install
