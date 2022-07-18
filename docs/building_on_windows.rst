Building Bitwuzla on Windows
============================

Important preamble
------------------

These steps document what is necessary to build a 64-bit version of
``pybitwuzla.pyd`` on 64-bit Windows. They also do not guarantee the correctness
of other parts of Bitwuzla (e.g., the main ``bitwuzla.exe``\ ).

To ensure the portability of ``pybitwuzla.pyd``\ , every effort is made in this
guide to avoid building Bitwuzla with Cygwin (e.g., we wish to avoid a
dependency on ``cygwin1.dll``\ , which could affect the portability of
``pybitwuzla.pyd``\ ). Given this, the guide is written to use the MinGW-w64
"cross-compiler". Steps are also taken to ensure that the resulting binaries
have no dependency on the MinGW DLLs either.

These notes are purposefully very detailed to allow for someone to go from a
completely fresh Windows 11 installation to a working version of Bitwuzla.

Finally, some of Bitwuzla's dependencies have been *heavily* modified to allow
them to build on Windows. This means that functionality such as timeouts might
be completely inoperable on Windows.

A note on licensing
^^^^^^^^^^^^^^^^^^^

Bitwuzla depends (amongst other libraries) on the GNU Multiple Precision
Arithmetic Library ("GMP"; https://gmplib.org/); GMP is dual-licensed under
both the GPL v2 and the LGPL v3.

The following guide builds GMP **as a shared library** and links Bitwuzla
against this shared library, to ensure that the resulting ``pybitwuzla.pyd``
can be distributed as liberally as possible (that is, the resulting
``pybitwuzla.pyd`` file will have LGPL components; linking GMP statically would
result in ``pybitwuzla.pyd`` having GPL components).

If you chose to distribute ``pybitwuzla.pyd`` that has been built in this way,
you are bound by the LGPL, and should include the LGPL licence text in any
distribution you make that includes these files.


Dependencies
------------

MinGW-w64
^^^^^^^^^

To build Bitwuzla, you require a build of GCC that supports building
applications on Windows. Typically, this compiler would be provided by the
MinGW-w64 project: https://www.mingw-w64.org/.

For the purposes of this guide, MinGW-w64 can be installed in two ways: by
downloading an official release from the MinGW-w64 SourceForce
(https://sourceforge.net/projects/mingw-w64/) or via the MSYS2 package
repositories.

If you chose to install MinGW-w64 outside of MSYS2, you should ensure that you
install a version that supports the `win32` threading model; the POSIX
threading model has not been tested at all for building Bitwuzla on Windows.
Furthermore, Bitwuzla's make system has been modified to statically link,
expecting the ``win32`` model.

The following release of MinGW-w64 was tested at the time of writing:

* Version: 8.1.0
* Architecture: x86_64
* Threads: win32
* Exception: seh (default)
* Build revision: 0 (default)

MSYS2
^^^^

Install MSYS2 from here:

* https://www.msys2.org

It is important to select the 64-bit installation option
(\ ``msys2-x86_64-<DATE>.exe``\ ). There are no further choices to be made when
installing MSYS.

Once MSYS is installed, start an MSYS shell, and run ``pacman -Syuu``. Once this
is complete, it will ask you to close the shell. Close MSYS, re-open it and
re-run ``pacman -Syuu`` again. Once it is complete the second time, close and
re-open MSYS. This process needs to be performed twice to allow for MSYS to
first update itself, and then update its packages.

Now install the following:

* ``pacman -S --needed make git vim wget patch tar m4``

If you wish to use MinGW-w64 installed through MSYS, then you should run the following:

* ``pacman -S --needed mingw-w64-x86_64-winpthreads``

At the time of writing, this installed GCC 12.1.0.

Python 3.10
^^^^^^^^^^^

Install the most recent 64-bit Python 3.10 from here:

* https://www.python.org/downloads/windows/

You should download the "Windows x86-64 executable installer". If you wish to
avoid Python being installed into your AppData folder, you should choose to
customise the installation, and select "Install for all users" (recommended for
the purposes of following these instructions).

Update your ``%PATH%`` variable to include both the path to ``python.exe`` and to
the ``Scripts`` sub-directory of the Python installation. These paths will look
something like:

* ``C:\Program Files\Python310``
* ``C:\Program Files\Python310\Scripts``

If you installed Python for only the current user, the paths will look
something like:

* ``C:\Users\%USERNAME%\AppData\Local\Programs\Python\Python310``
* ``C:\Users\%USERNAME%\AppData\Local\Programs\Python\Python310\scripts``

You need to ensure that these paths appear *before*
``%USERPROFILE%\AppData\Local\Microsoft\WindowsApps``\ , otherwise Window's
"wrapper" to *install* Python will get invoked.

Once your ``%PATH%`` is set correctly, start ``cmd`` and run the following:

.. code-block:: bash

  python -m pip install --upgrade pip
  python -m pip install --upgrade cython

If you installed Python system-wide (e.g., in to the default path of
``C:\Program Files\Python310``\ ), you should ensure that the above commands are run
inside of an administrative ``cmd``\ , such that the packages get installed into
the global Python installation.

CMake
^^^^^

The version of CMake that comes with MSYS does not correctly support MSYS
Makefiles (strangely). You should download the most recent version of CMake
from here:

* https://cmake.org/download/

Downloading "Windows win64-x64 ZIP" (\ ``cmake-<VERSION>-win64-x64.zip``\ ) is
sufficient. You do not need the installer.

When this is downloaded, extract the zip, but *remember the path you extracted
it to*\ ! You will need it later to the set the variable ``CMAKE_DIR``. The rest of
this guide assumes you have extracted CMake to the root of your ``C:`` drive.

*Note*: these instructions rely on the CMake environment variable
`CMAKE_GENERATOR` -- this places a minimum CMake version of 3.15 to build
Bitwuzla on Windows.

Building Bitwuzla
-----------------

Configuring Bitwuzla's build environment
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Now that you have installed all of the necessary dependencies for Bitwuzla, we
need to configure our build environment. Start an MSYS shell, enter the
directory you wish to build Bitwuzla in, and create a file called ``vars.sh``.
The file should have the following content:

.. code-block:: bash

   #!/bin/bash
   
   set -eu
   
   # **Important**
   #
   # If you installed Python for only the current user, pay particular attention
   # to the value of `PYTHON_DIR`. Before calling `cygpath -u`, call `cygpath -d`
   # to remove the space.
   #
   export PYTHON_DIR=$(cygpath -u $(cygpath -d "C:\Program Files\Python310"))
   export CMAKE_DIR=$(cygpath -u "C:\cmake-3.23.2-windows-x86_64")

   # If you've installed GCC via MinGW-w64 directly, your path might be:
   # export MINGW_DIR=$(cygpath -u "C:\mingw64\x86_64-8.1.0-release-win32-seh-rt_v6-rev0")

   # For an MSYS2 install of GCC from MinGW-w64, your path might be:
   export MINGW_DIR=$(cygpath -u "C:\msys64\mingw64")
   
   # MinGW-w64 must be *before* Python, to ensure `which` finds Python.org Python!
   export PATH=${MINGW_DIR}/bin:${PATH}
   export PATH=${PYTHON_DIR}:${PATH}
   export PATH=${PYTHON_DIR}/Scripts:${PATH}
   export PATH=${CMAKE_DIR}/bin:${PATH}
   
   export DEBUG_FLAG=""
   export COMPARCH=64

   # Additional flags to ensure that we always link statically (and suppress errors from multiple definitions, which happens due to statically link)
   export EXTRA_FLAGS="-static-libstdc++ -static-libgcc -Wl,-Bstatic,--whole-archive -lstdc++ -lwinpthread -Wl,-Bdynamic,--no-whole-archive -Wl,--allow-multiple-definition"
   
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
   
   # Ensure that CMake always uses MSYS Makefiles
   export CMAKE_GENERATOR="MSYS Makefiles"

   set +eu
   
   # EOF

Once you have created this file, you should run ``source vars.sh``. You should
now check the following:


* ``which gcc``
* ``which python``
* ``which cmake``
* ``which cython``

If any of these do not appear to look right, or return incorrect values, you
need to check your contents of ``vars.sh`` -- pay special attention to
``CMAKE_DIR`` and ``MINGW_DIR``\ !

Building GMP
^^^^^^^^^^^^

Once you have ``vars.sh`` configured to correctly configure your build
environment, you can build GMP as shared library.

To obtain a version of GMP:

.. code-block:: bash

   wget "https://gmplib.org/download/gmp/gmp-6.2.1.tar.xz"
   tar -xJvf gmp-6.2.1.tar.xz

The following steps will allow you to build Bitwuzla from the above clone:

.. code-block:: bash

   #!/bin/bash

   source vars.sh
   
   cd gmp-6.2.1
   
   ./configure --build=x86_64-w64-mingw64 --host=x86_64-w64-mingw64 --disable-static --enable-shared --enable-cxx  --prefix=$(readlink -f root)
   
   make -j$(nproc)
   
   make install -j$(nproc)

   # EOF

This will install GMP into the folder ``root`` inside of ``gmp-6.2.1``. The
rest of the guide expects that your ``gmp-6.2.1`` folder is next to your source
tree for Bitwuzla.

Obtaining Bitwuzla
^^^^^^^^^^^^^^^^^^

Now that you have configured your environment, you should obtain a copy of
Bitwuzla:

.. code-block:: bash

  git clone https://github.com/Bitwuzla/bitwuzla

Building
^^^^^^^^

The following steps will allow you to build Bitwuzla from the above clone:

.. code-block:: bash

   #!/bin/bash
   
   set -eu
   
   source vars.sh
   
   cd bitwuzla
   
   rm -rf deps
   
   #
   # Download, patch and build Bitwuzla's dependencies
   #
   ./contrib/setup-btor2tools.sh
   ./contrib/setup-cadical.sh
   ./contrib/setup-symfpu.sh
   
   #
   # Modify pybitwuzla.pyx to be "more Windows compatible"
   #
   ./contrib/fix_cython_windows.sh
   
   #
   # Build Bitwuzla
   #
   # Please pay careful attention to `CMAKE_PREFIX_PATH` (for the path to where
   # you installed GMP) and `PYTHON_EXECUTABLE` (to ensure we use Python.org
   # Python and not MinGW-w64 Python)
   #
   rm -rf build
   mkdir build
   cd build
   cmake .. -DPYTHON=ON -DUSE_SYMFPU=ON -DIS_WINDOWS_BUILD=1 -DCMAKE_PREFIX_PATH=$(readlink -f ../../gmp-6.2.1/root) -DPYTHON_EXECUTABLE:FILEPATH=$(readlink -f ${PYTHON_DIR}/python.exe)
   make -j12
   cd ..
   
   # EOF

*Notes:*

* On Windows, the above ``setup`` scripts automatically patch the version of
  Bitwuzla's dependencies to enable them to compile with Windows -- as per the
  start of this guide, these changes may dramatically change Bitwuzla's
  behaviour
* The use of ``-G "MSYS Makefiles"`` is *highly* essential to allow you to build
  Bitwuzla on Windows
* If you do not use a Python.org Python build, then your resulting
  ``pybitwuzla.pyd`` will likely depend on MinGW-w64 DLLs, making it harder to
  distribute

Packaging
^^^^^^^^^

On Windows, it is necessary to "collect-up" Bitwuzla's dependencies into one
directory before trying to work with our build artefacts. This can be achieved
as follows (run in the folder that contains GMP and your clone of Bitwuzla):

.. code-block:: bash

   #!/bin/bash

   dst=bitwuzla_build
   mkdir ${dst}

   cp gmp-6.2.1/root/bin/libgmp-10.dll ${dst}
   cp bitwuzla/build/bin/libbitwuzla.dll ${dst}
   cp bitwuzla/build/lib/pybitwuzla.pyd ${dst}

   # EOF

These steps are necessary as Windows resolves DLLs by looking either next to
the current DLL or by inspecting ``%PATH%``.

Testing Bitwuzla
^^^^^^^^^^^^^^^^

Now that you have built ``pybitwuzla.pyd`` and collected the necessary
artefacts, you can test your build:

.. code-block:: bash

   #!/bin/bash

   # this script presumes it is run from the common directory containing your `bitwuzla_build` folder
   python -m pip install --upgrade pytest
   export PYTHONPATH=$(cygpath -d $(readlink -f bitwuzla_build))
   echo -e "import pybitwuzla\nprint(dir(pybitwuzla))" | python
   python -m pytest bitwuzla/test/python/test_api.py

   # EOF

Please note, at the time of writing, tests that use `dump` are not expected to pass.

