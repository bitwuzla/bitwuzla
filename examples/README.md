Bitwuzla API Examples
=====================

This directory contains examples that illustrate how to use Bitwuzla's
C and Python APIs.

Build
-----

The examples in this directory are not built by default.
To build, issue the following commands.

```
mkdir <build_dir>
cd <build_dir>
cmake ..
make                     # use -jN to build with N threads
ctest                    # run all examples, use -jN to run with N threads
ctest -R <example>       # run <example>
./bin/path/to/<example>  # alternative way to run example
```

**Note:** If you installed Bitwuzla in a non-standard location, you have to
additionally specify `CMAKE_PREFIX_PATH` to point to the location of
`BitwuzlaConfig.cmake` (usually `<your-install-prefix>/lib/cmake`) as follows:

```
  cmake .. -DCMAKE_PREFIX_PATH=<your-install-prefix>/lib/cmake
```

The examples binaries are built into `<build_dir>/bin`.
