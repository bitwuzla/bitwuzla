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

KISSAT_DIR="${DEPS_DIR}/kissat"

rm -rf "${KISSAT_DIR}"

# Download and build Kissat

# This commit is version 2.0.1 which behaves identically to version
# sc2021-sweep but removes an unconditional runtime assertion ("coverage goal")
# and avoids the "undefined reference to `kissat_signal_name'" error that
# previously occured for some setups.
download_github arminbiere/kissat 02cd69626a53e93e09286b1978ccb5d6bec58b8e "${KISSAT_DIR}"
cd "${KISSAT_DIR}"

./configure -fPIC --quiet ${EXTRA_FLAGS}
make -j${NPROC}
install_lib build/libkissat.a
install_include src/kissat.h

