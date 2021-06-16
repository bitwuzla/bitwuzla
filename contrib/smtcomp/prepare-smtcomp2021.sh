#!/bin/sh

set -e -o pipefail

BUILD_DIR="$(pwd)/build"
BITWUZLA_BINARY="$BUILD_DIR/bin/bitwuzla"
YEAR="2021"

[ -d "$BUILD_DIR" ] && echo "build directory already exists" && exit 1

rm -rf "$(pwd)/deps"

./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh
./contrib/setup-lingeling.sh
./contrib/setup-symfpu.sh

./configure.sh --no-minisat --no-picosat --no-cms
(
  cd "$BUILD_DIR"
  make -j $(nproc)
)

b="$($BITWUZLA_BINARY --version)"
version="bitwuzla-${b}"

dir="/tmp/bitwuzla-smtcomp"
rm -rf $dir
RUN_DEFAULT="$dir/bin/starexec_run_default"
DESCRIPTION="$dir/starexec_description.txt"

archive=${version}.tar.gz
mkdir -p "$dir/bin"
cp "$BITWUZLA_BINARY" "$dir/bin"

cat > "$RUN_DEFAULT" << EOF
#!/bin/sh
./bitwuzla --smt-comp-mode \$1
EOF

echo "Bitwuzla $YEAR" > "$DESCRIPTION"
chmod +x "$RUN_DEFAULT"
tar -C "$dir" -zcf "$archive" .
ls -l "$archive"

rm -rf $dir
