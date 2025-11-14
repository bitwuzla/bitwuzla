Installation and Build Instructions
===================================

Building Bitwuzla on Linux and macOS
------------------------------------

.. code:: bash

  # Clone Bitwuzla repository
  git clone https://github.com/bitwuzla/bitwuzla
  cd bitwuzla

  # Configure Bitwuzla release build
  ./configure.py

  # Build and install
  cd build && ninja install   # or just `ninja` to only build Bitwuzla


.. note::
   If Bitwuzla is not installed, you can find the binary in ``build/src/main/``
   and the library in ``build/src/``.


* **Required Dependencies**

  * `Python >= 3.7 <https://www.python.org>`_
  * `Meson >= 0.64 <https://mesonbuild.com>`_
  * `Ninja <https://ninja-build.org>`_
  * `GMP >= v6.3 (GNU Multi-Precision arithmetic library) <https://gmplib.org>`_
  * `CaDiCaL >= 1.5.0 <https://github.com/arminbiere/cadical>`_
  * `SymFPU <https://github.com/martin-cs/symfpu>`_

* **Optional Dependencies**

  * `CryptoMiniSat <https://github.com/msoos/cryptominisat>`_
  * `Kissat <https://github.com/arminbiere/kissat>`_


.. note::
  If the build system does not find CaDiCaL or SymFPU, it will fall back to
  downloading and building a suitable version itself.

Python Bindings
---------------
.. code:: bash

  # Clone Bitwuzla repository
  git clone https://github.com/bitwuzla/bitwuzla
  cd bitwuzla

  # Build and install Bitwuzla Python bindings
  pip install .


For how to use the Python bindings, please refer to the :ref:`python-api`.

* **Required Dependencies**

  * `cython >= 3.0.0 <https://pypi.org/project/Cython>`_
  * `meson-python <https://pypi.org/project/meson-python>`_


Building without pip
^^^^^^^^^^^^^^^^^^^^

.. code:: bash

  # Clone Bitwuzla repository
  git clone https://github.com/bitwuzla/bitwuzla
  cd bitwuzla

  ./configure.py --python

  # Build Python bindings
  cd build && ninja python-bindings


.. note::
   The Python module can be found in ``build/src/api/python/``.


Building Bitwuzla for Windows
-----------------------------

Bitwulzla can be either cross-compiled via Mingw-w64 or MSYS2.

* **Required Dependencies**

The following `mingw` packages are required to compile Bitwuzla for Windows:

  * `mingw-w64-x86_64-gcc`
  * `mingw-w64-x86_64-gmp`
  * `mingw-w64-x86_64-meson`
  * `mingw-w64-x86_64-ninja`
  * `mingw-w64-x86_64-python3`
  * `mingw-w64-x86_64-cython` (optional for Python bindings)
  * `mingw-w64-x86_64-gtest` (optional for debug builds)
  * `mingw-w64-x86_64-python-pytest` (optional for debug builds)

On **arm64** machines, replace `x86_64` with `aarch64` for the packages above.
After setting up the MSYS2 environment, follow the Linux/macOS building
instructions.
For cross-compilation add flag `--win64` to the configure line.

.. code:: bash

  # Clone Bitwuzla repository
  git clone https://github.com/bitwuzla/bitwuzla
  cd bitwuzla

  # Configure Bitwuzla release build
  ./configure.py --win64

  # Build and install
  cd build && ninja


API Documentation
-----------------

The documentation for the latest stable release is available at:
https://bitwuzla.github.io/docs

You can build the documentation from the repository as follows.

.. code:: bash

   ./configure.py --docs --python

   cd build && ninja docs

The documentation can be found in ``build/docs/``.

* **Required Dependencies**

  * `Doxygen <https://www.doxygen.nl>`_
  * `Sphinx >= 1.2 <https://www.sphinx-doc.org>`_
  * `sphinxcontrib-bibtex <https://sphinxcontrib-bibtex.readthedocs.io>`_
  * `Breathe <https://breathe.readthedocs.io>`_


.. note::
   Configure with ``--python`` to include the documentation for the Python
   bindings.

Code Coverage Reports
---------------------

.. code:: bash

   # Generate code coverage reports for debug build
   ./configure.py debug --coverage

   cd build && meson test && ninja coverage


.. note::
   The code coverage reports can be found in ``build/meson-logs/``.

