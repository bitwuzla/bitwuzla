#!/bin/bash
# Build GMP and MPFR from source for manylinux wheel builds.
# manylinux_2_28 ships versions too old for Bitwuzla.

set -euo pipefail

PREFIX=/usr/local
GMP_VERSION=6.3.0
MPFR_VERSION=4.2.2

dnf install -y gcc gcc-c++ make m4 texinfo

# Build GMP
curl -sSL https://ftp.gnu.org/gnu/gmp/gmp-${GMP_VERSION}.tar.xz -o /tmp/gmp.tar.xz
tar xf /tmp/gmp.tar.xz -C /tmp
cd /tmp/gmp-${GMP_VERSION}
CFLAGS="-fPIC" CXXFLAGS="-fPIC" ./configure --prefix=${PREFIX} --enable-static --disable-shared --enable-cxx --with-pic
make -j"$(nproc)"
make install

# Build MPFR
curl -sSL https://ftp.gnu.org/gnu/mpfr/mpfr-${MPFR_VERSION}.tar.xz -o /tmp/mpfr.tar.xz
tar xf /tmp/mpfr.tar.xz -C /tmp
cd /tmp/mpfr-${MPFR_VERSION}
CFLAGS="-fPIC" CXXFLAGS="-fPIC" ./configure --prefix=${PREFIX} --enable-static --disable-shared --with-gmp=${PREFIX} --enable-cxx --with-pic
make -j"$(nproc)"
make install

# Ensure pkg-config can find them
export PKG_CONFIG_PATH=${PREFIX}/lib/pkgconfig:${PREFIX}/lib64/pkgconfig:${PKG_CONFIG_PATH:-}
pkg-config --modversion gmp mpfr
