#!/bin/bash

set -e

YEAR=2024
DIST_NAME=bitwuzla-0.5.0-dev
BUILD_DIR=$(pwd)/build-smtcomp-$YEAR
DOCKER_DIR=$(pwd)/contrib/smtcomp/$YEAR

rm -rf "$BUILD_DIR"

# Include sources for all required subprojects
meson setup "$BUILD_DIR" \
  --buildtype release \
  --force-fallback-for=cadical,gmp,symfpu

pushd "$BUILD_DIR"
  meson dist --include-subprojects
  cp meson-dist/$DIST_NAME.tar.xz "$DOCKER_DIR/bitwuzla-src.tar.xz"
popd

pushd "$DOCKER_DIR"
  docker build --output=. --target=bitwuzla_binary .
  zip bitwuzla-submission-smtcomp-$YEAR.zip \
    Dockerfile \
    bin/bitwuzla \
    Dockerfile \
    bitwuzla-src.tar.xz \
    Readme.md
  sha256sum bitwuzla-submission-smtcomp-$YEAR.zip
popd
