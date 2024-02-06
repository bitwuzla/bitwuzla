Bitwuzla API Examples
=====================

This directory contains examples that illustrate how to use Bitwuzla's
C, C++ and Python APIs.

Build
-----

The examples in this directory are not built by default.
To build, issue the following commands.

```
meson setup <build_dir>
cd <build_dir>
meson compile
meson test               # run all examples (stdout output not printed)
meson test -v            # run all examples (stdout output printed)
./<path>/<example>       # alternative way to run example
```

**Note:** If you installed Bitwuzla in a non-standard location, you have to
additionally specify the path to the `pkgconfig` directory before when calling
`meson setup` as follows:
```
meson setup <build_dir> --pkg-config-path=<your-install-prefix>/lib/pkgconfig
```

The examples binaries are built into `<build_dir>/<path>`, where `<path>`
mirrors the path to the source files, e.g., `<build_dir>/c/quickstart` for
example `c/quickstart.c`.

To enable Python examples in the test suite, configure the build directory
with a path to the Bitwuzla Python module. For the non-standard
location from above, call `meson setup` as follows:
```
meson setup <build_dir> --pkg-config-path=<your-install-prefix>/lib/pkgconfig \
    -Dpython_path=<your-install-prefix>/lib/python<version>/site-packages/
```
Python Examples can also be run manually via
`python python/<example_name>`, e.g., `python python/quickstart.py`.
