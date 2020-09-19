#!/usr/bin/env bash

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

PICOSAT_DIR=${DEPS_DIR}/picosat

rm -rf ${PICOSAT_DIR}

# Download and build PicoSAT
curl -o picosat-965.tar.gz -L http://fmv.jku.at/picosat/picosat-965.tar.gz
tar xzf picosat-965.tar.gz
rm picosat-965.tar.gz
mv picosat-965 ${PICOSAT_DIR}
cd ${PICOSAT_DIR}

if is_windows; then
  component="PicoSAT"
  last_patch_date="20190110"
  test_apply_patch "${component}" "${last_patch_date}"
  EXTRA_FLAGS="--optimize --no-stats --no-trace"
fi

./configure.sh --shared ${EXTRA_FLAGS}
make -j${NPROC} libpicosat.a libpicosat.so
install_lib libpicosat.a
install_lib libpicosat.so
install_include picosat.h
