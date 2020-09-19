#!/usr/bin/env bash

set -e -o pipefail

./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh
./contrib/setup-cms.sh
./contrib/setup-lingeling.sh
./contrib/setup-minisat.sh
./contrib/setup-picosat.sh
