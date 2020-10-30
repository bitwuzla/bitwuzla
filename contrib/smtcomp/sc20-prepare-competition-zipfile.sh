#!/bin/sh

BUILD_DIR="$(pwd)/build"
BITWUZLA_BINARY="$BUILD_DIR/bin/cbitwuzla"
YEAR="2020"

[ -d "$BUILD_DIR" ] && echo "build directory already exists" && exit 1

rm -rf "$(pwd)/deps"

./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh
./contrib/setup-lingeling.sh
./contrib/setup-symfpu.sh

./configure.sh --no-minisat --no-picosat --no-cms --gmp --symfpu
(
  cd "$BUILD_DIR" || exit 1
  make -j $(nproc)
)

b=$($BITWUZLA_BINARY -v /dev/null | grep -i version | grep -i bitwuzla | awk '{print $(NF-1);exit}')
version=cbitwuzla-${b}

dir="/tmp/cbitwuzla-smtcomp"
rm -rf $dir
RUN_DEFAULT="$dir/bin/starexec_run_default"
DESCRIPTION="$dir/starexec_description.txt"

archive=${version}.tar.gz
mkdir -p "$dir/bin"
cp "$BITWUZLA_BINARY" "$dir/bin"

cat > "$RUN_DEFAULT" << EOF
#!/bin/sh
./cbitwuzla --smt-comp-mode \$1
EOF

echo "CBitwuzla $YEAR" > "$DESCRIPTION"
chmod +x "$RUN_DEFAULT"
tar -C "$dir" -zcf "$archive" .
ls -l "$archive"

rm -rf $dir
