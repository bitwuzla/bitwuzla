#!/bin/sh
#--------------------------------------------------------------------------#

BUILDDIR=build

#--------------------------------------------------------------------------#

build=default

assertions=no
units=unknown

asan=no
ubsan=no

shared=no
prefix=
path=

gcov=no
gprof=no

ninja=no

flags=""

#--------------------------------------------------------------------------#

usage () {
cat <<EOF
usage: $0 [<build type>] [<option> ...]

where <option> is one of the following:

  -h, --help        print this message and exit

  -f...|-m...       add compiler options

  --ninja           use Ninja build system
  --prefix <dir>    install prefix

  --path <dir>      look for dependencies in <dir>/{include,lib}
                    specify multiple --path options for multiple directories

  --shared          shared library

  --assertions      enable assertions (default: enabled for debug,
                                                disabled for production)
  --unit-testing    enable unit testing
  --no-unit-testing disable unit testing

  --asan            compile with -fsanitize=address -fsanitize-recover=address
  --ubsan           compile with -fsanitize=undefined
  --gcov            compile with -fprofile-arcs -ftest-coverage
  --gprof           compile with -pg
EOF
  exit 0
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

[ ! -e src/bitvector.cpp ] && die "$0 not called from bzla-ls base directory"

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

    --assertions) assertions=yes;;

    --asan)  asan=yes;;
    --ubsan) ubsan=yes;;
    --gcov)  gcov=yes;;
    --gprof) gprof=yes;;

    --unit-testing) units=ON;;
    --no-unit-testing) units=OFF;;

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

[ $units != unknown ] && cmake_opts="$cmake_opts -DTESTING=$units"

[ $ninja = yes ] && cmake_opts="$cmake_opts -G Ninja"

[ $assertions = yes ] && cmake_opts="$cmake_opts -DASSERTIONS=ON"
[ $asan = yes ] && cmake_opts="$cmake_opts -DASAN=ON"
[ $ubsan = yes ] && cmake_opts="$cmake_opts -DUBSAN=ON"
[ $shared = yes ] && cmake_opts="$cmake_opts -DBUILD_SHARED_LIBS=ON"

[ -n "$prefix" ] && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$prefix"
[ -n "$path" ] && cmake_opts="$cmake_opts -DCMAKE_PREFIX_PATH=$path"

[ $gcov = yes ] && cmake_opts="$cmake_opts -DGCOV=ON"
[ $gprof = yes ] && cmake_opts="$cmake_opts -DGPROF=ON"

[ -n "$flags" ] && cmake_opts="$cmake_opts -DFLAGS=$flags"

mkdir -p $BUILDDIR
cd $BUILDDIR || exit 1

[ -e CMakeCache.txt ] && rm CMakeCache.txt
cmake .. $cmake_opts
