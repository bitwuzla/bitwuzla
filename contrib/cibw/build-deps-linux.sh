#!/bin/bash
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2026 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

# Build GMP and MPFR from source for manylinux wheel builds.
# manylinux_2_28 ships versions too old for Bitwuzla.

set -euo pipefail

PREFIX=/usr/local
GMP_VERSION=6.3.0
MPFR_VERSION=4.2.2

dnf install -y gcc gcc-c++ make m4 texinfo

# CFLAGS replaces the flags GMP would choose, so it must include optimization.
# GMP 6.3.0's configure checks fail under C23, the default of newer compilers.
export CFLAGS="-O2 -std=gnu17"
export CXXFLAGS="-O2"

# Build GMP
curl -sSL https://ftp.gnu.org/gnu/gmp/gmp-${GMP_VERSION}.tar.xz -o /tmp/gmp.tar.xz
tar xf /tmp/gmp.tar.xz -C /tmp
cd /tmp/gmp-${GMP_VERSION}
# Target the generic CPU of the architecture rather than the CPU of the build
# machine, which may have instructions that the users' CPUs lack. On x86_64,
# a fat build still selects optimized assembly at runtime.
build=$(sh ./configfsf.guess)
case "$build" in
  x86_64-*) fat=--enable-fat ;;
  *) fat=--disable-fat ;;
esac
./configure --prefix="$PREFIX" --libdir="$PREFIX/lib" --build="$build" "$fat" \
  --enable-static --disable-shared --enable-cxx --with-pic
make -j"$(nproc)"
make install

# Build MPFR
curl -sSL https://ftp.gnu.org/gnu/mpfr/mpfr-${MPFR_VERSION}.tar.xz -o /tmp/mpfr.tar.xz
tar xf /tmp/mpfr.tar.xz -C /tmp
cd /tmp/mpfr-${MPFR_VERSION}
./configure --prefix="$PREFIX" --libdir="$PREFIX/lib" --with-gmp="$PREFIX" \
  --enable-static --disable-shared --with-pic
make -j"$(nproc)"
make install

PKG_CONFIG_PATH=$PREFIX/lib/pkgconfig pkg-config --modversion gmp mpfr
