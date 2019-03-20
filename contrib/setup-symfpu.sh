#!/bin/bash

source "$(dirname "$0")/setup-utils.sh"

SYMFPU_DIR=${DEPS_DIR}/symfpu

commit="1273dc9379b36af1461fe04aa453db82408006cf"

# Download and build symfpu
git clone https://github.com/martin-cs/symfpu.git ${SYMFPU_DIR}
cd ${SYMFPU_DIR}
git checkout $commit
install_include core symfpu
install_include utils symfpu
