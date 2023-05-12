#!/bin/bash

set -e -o pipefail

BUILD_DIR="$(pwd)/build-comp"
BITWUZLA_BINARY="$BUILD_DIR/src/main/bitwuzla"
YEAR="2023"

[ -d "$BUILD_DIR" ] && echo "build directory $BUILD_DIR already exists" && exit 1

meson setup $BUILD_DIR
(
  cd "$BUILD_DIR"
  ninja
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
./bitwuzla \$1
EOF

echo "Bitwuzla $YEAR" > "$DESCRIPTION"
chmod +x "$RUN_DEFAULT"
tar -C "$dir" -zcf "$archive" .
ls -l "$archive"

rm -rf $dir
