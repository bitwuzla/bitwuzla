#!/bin/bash

CONTRIB_DIR=$(dirname $(realpath -s $0))

source "$CONTRIB_DIR/setup-utils.sh"

SYMFPU_DIR="${DEPS_DIR}/symfpu"

commit="8fbe139bf0071cbe0758d2f6690a546c69ff0053"

# Download and build symfpu
git clone https://github.com/martin-cs/symfpu.git "${SYMFPU_DIR}"
cd "${SYMFPU_DIR}"
git checkout $commit
git apply "$CONTRIB_DIR/symfpu_202012001.patch"
install_include core symfpu
install_include utils symfpu
