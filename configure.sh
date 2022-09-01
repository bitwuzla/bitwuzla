#!/bin/sh
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

#--------------------------------------------------------------------------#

BUILDDIR=build

#--------------------------------------------------------------------------#

build=default

asan=no
ubsan=no
assertions=no
log=no
shared=no
prefix=
path=

testing=unknown

cadical=unknown
cms=unknown
kissat=unknown
lingeling=unknown
minisat=unknown
picosat=unknown

gcov=no
gprof=no
python=no
timestats=no

docs=no

ninja=no

flags=""

#--------------------------------------------------------------------------#

usage () {
cat <<EOF
usage: $0 [<build type>] [<option> ...]

Build types:

  production
  debug

Options:

  -h, --help        print this message and exit

  -f...|-m...       add compiler options

  --ninja           use Ninja build system
  --prefix <dir>    install prefix

  --path <dir>      look for dependencies in <dir>/{include,lib}
                    specify multiple --path options for multiple directories

  --shared          shared library

  -l                compile with logging support (default for '-g')
  --assertions      enable assertions (default: enabled in debug,
                                                disabled in production)
  --asan            compile with -fsanitize=address -fsanitize-recover=address
  --ubsan           compile with -fsanitize=undefined
  --gcov            compile with -fprofile-arcs -ftest-coverage
  --gprof           compile with -pg

  --python          compile python API
  --time-stats      compile with time statistics

  --testing         enable unit and regression testing
  --no-testing      disable unit and regression testing

  --docs            build API documentation

By default all supported SAT solvers available are used and linked.
If explicitly enabled, configuration will fail if the SAT solver library
can not be found.

  --no-cadical           do not use CaDiCaL
  --no-cms               do not use CryptoMiniSat
  --no-kissat            do not use Kissat
  --no-lingeling         do not use Lingeling
  --no-minisat           do not use MiniSAT
  --no-picosat           do not use PicoSAT

  --only-cadical         only use CaDiCaL
  --only-cms             only use CryptoMiniSat
  --only-kissat          only use Kissat
  --only-lingeling       only use Lingeling
  --only-minisat         only use MiniSAT
  --only-picosat         only use PicoSAT
EOF
  exit 0
}

reset_sat_solvers() {
  cadical=no
  cms=no
  kissat=no
  lingeling=no
  minisat=no
  picosat=no
}

#--------------------------------------------------------------------------#

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}

msg () {
  echo "[configure.sh] $*"
}

#--------------------------------------------------------------------------#

[ ! -e src/bzlamain.c ] && die "$0 not called from Bitwuzla base directory"

while [ $# -gt 0 ]
do
  opt=$1
  case $opt in
    -h|--help) usage;;

    -f*|-m*) if [ -z "$flags" ]; then flags=$1; else flags="$flags;$1"; fi;;

    --ninja) ninja=yes;;

    --prefix)
      shift
      [ $# -eq 0 ] && die "missing argument to $opt"
      prefix=$1
      ;;

    --path)
      shift
      [ $# -eq 0 ] && die "missing argument to $opt"
      [ -n "$path" ] && path="$path;"
      path="$path$1"
      ;;

    --shared) shared=yes;;

    -l)      log=yes;;
    --assertions) assertions=yes;;
    --asan)  asan=yes;;
    --ubsan) ubsan=yes;;
    --gcov)  gcov=yes;;
    --gprof) gprof=yes;;

    --python)     python=yes;;
    --time-stats) timestats=yes;;

    --testing) testing=yes;;
    --no-testing) testing=no;;

    --docs) docs=yes;;

    --no-cadical)   cadical=no;;
    --no-cms)       cms=no;;
    --no-kissat)    kissat=no;;
    --no-lingeling) lingeling=no;;
    --no-minisat)   minisat=no;;
    --no-picosat)   picosat=no;;

    --only-cadical)   reset_sat_solvers;cadical=yes;;
    --only-cms)       reset_sat_solvers;cms=yes;;
    --only-kissat)    reset_sat_solvers;kissat=yes;;
    --only-lingeling) reset_sat_solvers;lingeling=yes;;
    --only-minisat)   reset_sat_solvers;minisat=yes;;
    --only-picosat)   reset_sat_solvers;picosat=yes;;

    -*) die "invalid option '$opt' (try '-h')";;

    *) case $1 in
         production)      build=Production;;
         debug)           build=Debug;;
         *)               die "invalid build type (try -h)";;
       esac
       ;;
  esac
  shift
done

#--------------------------------------------------------------------------#

cmake_opts="$CMAKE_OPTS"

[ $build != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=$build"

[ $ninja = yes ] && cmake_opts="$cmake_opts -G Ninja"

[ $asan = yes ] && cmake_opts="$cmake_opts -DASAN=ON"
[ $ubsan = yes ] && cmake_opts="$cmake_opts -DUBSAN=ON"
[ $assertions = yes ] && cmake_opts="$cmake_opts -DASSERTIONS=ON"
[ $log = yes ] && cmake_opts="$cmake_opts -DLOG=ON"
[ $shared = yes ] && cmake_opts="$cmake_opts -DBUILD_SHARED_LIBS=ON"

[ -n "$prefix" ] && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$prefix"
[ -n "$path" ] && cmake_opts="$cmake_opts -DCMAKE_PREFIX_PATH=$path"

[ $testing = yes ] && cmake_opts="$cmake_opts -DTESTING=ON"
[ $testing = no ] && cmake_opts="$cmake_opts -DTESTING=OFF"

[ $cadical = yes ] && cmake_opts="$cmake_opts -DUSE_CADICAL=ON"
[ $cms = yes ] && cmake_opts="$cmake_opts -DUSE_CMS=ON"
[ $kissat = yes ] && cmake_opts="$cmake_opts -DUSE_KISSAT=ON"
[ $lingeling = yes ] && cmake_opts="$cmake_opts -DUSE_LINGELING=ON"
[ $minisat = yes ] && cmake_opts="$cmake_opts -DUSE_MINISAT=ON"
[ $picosat = yes ] && cmake_opts="$cmake_opts -DUSE_PICOSAT=ON"

[ $cadical = no ] && cmake_opts="$cmake_opts -DUSE_CADICAL=OFF"
[ $cms = no ] && cmake_opts="$cmake_opts -DUSE_CMS=OFF"
[ $kissat = no ] && cmake_opts="$cmake_opts -DUSE_KISSAT=OFF"
[ $lingeling = no ] && cmake_opts="$cmake_opts -DUSE_LINGELING=OFF"
[ $minisat = no ] && cmake_opts="$cmake_opts -DUSE_MINISAT=OFF"
[ $picosat = no ] && cmake_opts="$cmake_opts -DUSE_PICOSAT=OFF"

[ $gcov = yes ] && cmake_opts="$cmake_opts -DGCOV=ON"
[ $gprof = yes ] && cmake_opts="$cmake_opts -DGPROF=ON"

[ $python = yes ] && cmake_opts="$cmake_opts -DPYTHON=ON"
[ $timestats = yes ] && cmake_opts="$cmake_opts -DTIME_STATS=ON"

[ $docs = yes ] && cmake_opts="$cmake_opts -DDOCS=ON"

[ -n "$flags" ] && cmake_opts="$cmake_opts -DFLAGS=$flags"

mkdir -p $BUILDDIR
cd $BUILDDIR || exit 1

[ -e CMakeCache.txt ] && rm CMakeCache.txt
cmake .. $cmake_opts
