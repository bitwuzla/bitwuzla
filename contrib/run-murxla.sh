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

# Set up Murxla (https://github.com/murxla/murxla) and fuzz the current code.
#
# Everything lives in build-murxla/: a shared debug build of Bitwuzla installed
# into build-murxla/install and a Murxla checkout built against it. Both are
# only set up if not present, the Bitwuzla library is reinstalled on every run
# so that Murxla always fuzzes the current code.
#
# Usage: contrib/run-murxla.sh [<murxla options>]
#        contrib/run-murxla.sh --coverage[-keep] [<murxla options>]
#        contrib/run-murxla.sh --coverage-report
#
# Without options Murxla runs in continuous mode with a 5s time limit per test
# run and delta debugs the traces it finds. Error traces are written to the
# current working directory.
#
# Coverage mode instruments Bitwuzla and writes a report when Murxla exits. It
# uses its own build tree (build-murxla-cov/) because the setup steps below
# only configure a build tree that does not exist yet. Counters are reset on
# startup, --coverage-keep instead accumulates onto the data of previous
# sessions and --coverage-report only regenerates the report from the data on
# disk.

set -e -o pipefail

MURXLA_REPO="https://github.com/murxla/murxla.git"

COVERAGE=0
REPORT_ONLY=0
KEEP_DATA=0
while [ $# -gt 0 ]; do
  case "$1" in
    --coverage)        COVERAGE=1; shift ;;
    --coverage-keep)   COVERAGE=1; KEEP_DATA=1; shift ;;
    --coverage-report) COVERAGE=1; REPORT_ONLY=1; shift ;;
    *) break ;;
  esac
done

BITWUZLA_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [ "$COVERAGE" = 1 ]; then
  BUILD_DIR="${BUILD_DIR:-$BITWUZLA_DIR/build-murxla-cov}"
else
  BUILD_DIR="${BUILD_DIR:-$BITWUZLA_DIR/build-murxla}"
fi
INSTALL_DIR="$BUILD_DIR/install"
MURXLA_DIR="$BUILD_DIR/murxla"
MURXLA_BINARY="$MURXLA_DIR/build/bin/murxla"
COVERAGE_DIR="$BUILD_DIR/coverage"
COVERAGE_REPORT="$COVERAGE_DIR/index.html"

# Only report on Bitwuzla's own sources. Murxla is built inside $BUILD_DIR and
# is instrumented as well, and the counters of the subprojects say nothing
# about how well Murxla covers Bitwuzla. Parse errors are ignored since runs
# killed on timeout can leave a truncated counter file behind.
generate_coverage_report()
{
  mkdir -p "$COVERAGE_DIR"
  gcovr --root "$BITWUZLA_DIR" --filter "$BITWUZLA_DIR/src/" \
    --gcov-ignore-parse-errors -j "$(nproc)" --print-summary \
    --html-details "$COVERAGE_REPORT" --txt "$COVERAGE_DIR/coverage.txt" \
    "$BUILD_DIR/src"
  echo "-- coverage report: $COVERAGE_REPORT"
}

if [ "$REPORT_ONLY" = 1 ]; then
  generate_coverage_report
  exit 0
fi

configure_args=()
murxla_cmake_args=()
if [ "$COVERAGE" = 1 ]; then
  configure_args=(--coverage)
  # MURXLA_COVERAGE makes Murxla dump the counters from its SIGABRT handler so
  # that aborted and timed out runs contribute coverage, too. Murxla itself has
  # to be built with --coverage to get libgcov, which provides __gcov_dump(),
  # the instrumented Bitwuzla library does not export it.
  murxla_cmake_args=(-DCMAKE_CXX_FLAGS="--coverage -DMURXLA_COVERAGE"
                     -DCMAKE_EXE_LINKER_FLAGS="--coverage")
fi

# Debug build so that assertions and model/unsat core checks are enabled.
if [ ! -f "$BUILD_DIR/build.ninja" ]; then
  echo "-- configuring Bitwuzla in $BUILD_DIR"
  (
    cd "$BITWUZLA_DIR"
    python3 configure.py debug --shared --no-testing "${configure_args[@]}" \
      --prefix "$INSTALL_DIR" -b "$BUILD_DIR"
  )
  # Keep debug symbols in the installed library, they are stripped by default.
  meson configure "$BUILD_DIR" -Dstrip=false
fi

# Rebuilds first, --only-changed skips copying the (large) unchanged libraries.
echo "-- installing Bitwuzla into $INSTALL_DIR"
meson install -C "$BUILD_DIR" --only-changed

if [ ! -d "$MURXLA_DIR" ]; then
  echo "-- cloning Murxla into $MURXLA_DIR"
  git clone "$MURXLA_REPO" "$MURXLA_DIR"
fi

# Murxla picks up Bitwuzla via install/lib/pkgconfig/bitwuzla.pc and links
# libbitwuzla.so by absolute path, hence it does not have to be rebuilt when
# Bitwuzla changes.
if [ ! -f "$MURXLA_BINARY" ]; then
  echo "-- building Murxla in $MURXLA_DIR/build"
  cmake -S "$MURXLA_DIR" -B "$MURXLA_DIR/build" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_PREFIX_PATH="$INSTALL_DIR" \
    "${murxla_cmake_args[@]}" \
    -DENABLE_BOOLECTOR=OFF \
    -DENABLE_CVC5=OFF \
    -DENABLE_YICES=OFF
  cmake --build "$MURXLA_DIR/build" -j "$(nproc)"
fi

args=("$@")
if [ ${#args[@]} -eq 0 ]; then
  args=(-t 5 -d)
fi
# Traces already encode the solver, --bitwuzla must not be given on replay.
case " ${args[*]} " in
  *" -u "* | *" --untrace "*) ;;
  *) args=(--bitwuzla "${args[@]}") ;;
esac

# Counter files accumulate over runs and go stale on recompilation.
if [ "$COVERAGE" = 1 ] && [ "$KEEP_DATA" = 0 ]; then
  echo "-- resetting coverage counters"
  find "$BUILD_DIR" -name '*.gcda' -delete
fi

echo "-- $MURXLA_BINARY ${args[*]}"
if [ "$COVERAGE" = 0 ]; then
  exec "$MURXLA_BINARY" "${args[@]}"
fi

# Ctrl+C terminates Murxla gracefully, keep the wrapper alive so that it still
# generates the report. This installs a handler instead of ignoring the signal,
# an ignored disposition would be inherited by Murxla.
trap 'echo' INT
"$MURXLA_BINARY" "${args[@]}" || true
generate_coverage_report
