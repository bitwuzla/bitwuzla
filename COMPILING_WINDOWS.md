# Boolector installation steps on Windows

### Important preamble

These steps document what is necessary to build a 64-bit version of `pyboolector.pyd` on 64-bit Windows. They also do not guarantee the correctness of other parts of Boolector (e.g., the main `boolector.exe`).

To ensure the portability of `pyboolector.pyd`, every effort is made in this guide to avoid building Boolector with Cygwin (e.g., we wish to avoid a dependency on `cygwin1.dll`, which could affect the portability of `pyboolector.pyd`). Given this, the guide is written to use the MinGW-W64 "cross-compiler".

These notes are purposefully very detailed to allow for someone to go from a completely fresh Windows 10 installation to a working version of Boolector.

Finally, some of Boolector's dependencies have been _heavily_ modified to allow them to build on Windows. This means that functionality such as timeouts might be completely inoperable on Windows.


## Dependencies

### MinGW

Install MinGW-W64 from here:

* <https://sourceforge.net/projects/mingw-w64/files/mingw-w64/mingw-w64-release/>

You should select the "MinGW-W64 Online Installer" (`MinGW-W64-install.exe`).

The following options are recommended and have been tested when writing this guide:

* Version: 8.1.0
* Architecture: x86_64
* Threads: win32
* Exception: seh (default)
* Build revision: 0 (default)

When selecting the threading model, only the `win32` threading model has been validated -- the POSIX model has not been tested at all. On Windows, Boolector's make system has been modified to statically link, expecting the `win32` model.


### MSYS

Install MSYS from here:

* <https://www.msys2.org>

It is important to select the 64-bit installation option (`msys2-x86_64-<DATE>.exe`). There are no further choices to be made when installing MSYS.

Once MSYS is installed, start an MSYS shell, and run `pacman -Syuu`. Once this is complete, it will ask you to close the shell. Close MSYS, re-open it and re-run `pacman -Syuu` again. Once it is complete the second time, close and re-open MSYS. This process needs to be performed twice to allow for MSYS to first update itself, and then update its packages.

Now install the following:

* `pacman -S --needed make git vim wget patch tar`


### Python 3.8

Install the most recent 64-bit Python 3.8 from here:

* <https://www.python.org/downloads/windows/>

You should download the "Windows x86-64 executable installer". If you wish to avoid Python being installed into your AppData folder, you should choose to customise the installation, and select "Install for all users" (recommended for the purposes of following these instructions).

Update your `%PATH%` variable to include both the path to `python.exe` and to the `Scripts` sub-directory of the Python installation. These paths will look something like:

* `C:\Program Files\Python38`
* `C:\Program Files\Python38\Scripts`

If you installed Python for only the current user, the paths will look something like:

* `C:\Users\%USERNAME%\AppData\Local\Programs\Python\Python38`
* `C:\Users\%USERNAME%\AppData\Local\Programs\Python\Python38\scripts`

You need to ensure that these paths appear *before* `%USERPROFILE%\AppData\Local\Microsoft\WindowsApps`, otherwise Window's "wrapper" to _install_ Python will get invoked.

Once your `%PATH%` is set correctly, start `cmd` and run the following:

* `python -m pip install --upgrade pip`
* `python -m pip install --upgrade cython`

If you installed Python system-wide (e.g., in to the default path of `C:\Program Files\Python38`), you should ensure that the above commands are run inside of an administrative `cmd`, such that the packages get installed into the global Python installation.


### CMake

The version of CMake that comes with MSYS does not correctly support MSYS Makefiles (strangely). You should download the most recent version of CMake from here:

* <https://cmake.org/download/>

Downloading "Windows win64-x64 ZIP" (`cmake-<VERSION>-win64-x64.zip`) is sufficient. You do not need the installer.

When this is downloaded, extract the zip, but _remember the path you extracted it to_! You will need it later to the set the variable `CMAKE_DIR`. The rest of this guide assumes you have extracted CMake to the root of your `C:` drive.


## Building Boolector

### Configuring Boolector's build environment

Now that you have installed all of the necessary dependencies for Boolector, we need to configure our build environment. Start an MSYS shell, enter the directory you wish to build Boolector in, and create a file called `vars.sh`. The file should have the following content:

```bash
#!/bin/bash

set -eu

# **Important**
#
# If you installed Python for only the current user, pay particular attention
# to the value of `PYTHON_DIR`. Before calling `cygpath -u`, call `cygpath -d`
# to remove the space.
#
export PYTHON_DIR=$(cygpath -u $(cygpath -d "C:\Program Files\Python38"))

export CMAKE_DIR=$(cygpath -u "C:\cmake-3.17.3-win64-x64")
export MINGW_DIR=$(cygpath -u "C:\Program Files\mingw-w64\x86_64-8.1.0-win32-seh-rt_v6-rev0\mingw64")

export PATH=${PYTHON_DIR}:${PATH}
export PATH=${PYTHON_DIR}/Scripts:${PATH}
export PATH=${CMAKE_DIR}/bin:${PATH}
export PATH=${MINGW_DIR}/bin:${PATH}

export DEBUG_FLAG=""
export COMPARCH=64

export EXTRA_FLAGS="-static-libstdc++ -static-libgcc"

# -DMS_WIN64 is required so the Python headers properly detect a 64-bit build
export COMPFLAGS="${EXTRA_FLAGS} -I${PYTHON_DIR}/include -m${COMPARCH} -DMS_WIN64"

if [ -z "$DEBUG_FLAG" ]; then
    COMPFLAGS="-O3 -DNDEBUG ${COMPFLAGS}"
fi

export CFLAGS="${COMPFLAGS} -std=gnu11"
export CXXFLAGS="${COMPFLAGS} -std=gnu++11"
export PYTHON_INCLUDE="${COMPFLAGS}"
export LDFLAGS="${EXTRA_FLAGS} -L${PYTHON_DIR}/lib"

export CC="gcc"
export CXX="g++"

set +eu

# EOF
```

Once you have created this file, you should run `source vars.sh`. You should now check the following:

* `which gcc`
* `which python`
* `which cmake`
* `which cython`

If any of these do not appear to look right, or return incorrect values, you need to check your contents of `vars.sh` -- pay special attention to `CMAKE_DIR` and `MINGW_DIR`!


### Obtaining Boolector

Now that you have configured your environment, you should obtain a copy of Boolector:

* `git clone https://github.com/Boolector/boolector`


### Building Boolector

The following steps will allow you to build Boolector from the above clone:

```bash
#!/bin/bash

set -eu

cd boolector

#
# Download, patch and build Boolector's dependencies
#

./contrib/setup-picosat.sh
./contrib/setup-lingeling.sh
./contrib/setup-cadical.sh
./contrib/setup-btor2tools.sh

#
# Modify pyboolector.pyx to be "more Windows compatible"
#
./contrib/fix_cython_windows.sh

#
# Build Boolector
#
mkdir build
cd build
cmake .. -DPYTHON=ON -DIS_WINDOWS_BUILD=1 -G "MSYS Makefiles"
make -j12
cd ..

# EOF
```

_Notes:_

* On Windows, the above `setup` scripts automatically patch the version of Boolector's dependencies to enable them to compile with Windows -- as per the start of this guide, these changes may dramatically change Boolector's behaviour.
* The use of `-G "MSYS Makefiles"` is _highly_ essential to allow you to build Boolector on Windows.


### Testing Boolector

Now that you have built `pyboolector.pyd`, you can test it:

```bash
#!/bin/bash

# this script presumes it is run from the root of the Boolector clone

export PYTHONPATH=$(cygpath -d $(readlink -f build/lib))
python examples/api/python/api_usage_examples.py

# EOF
```

If you get uncaught exceptions on `splice`, then you probably did not run `./contrib/fix_cython_windows.sh` before building.

