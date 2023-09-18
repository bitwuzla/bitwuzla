Installation and Build Instructions
===================================

Building Bitwuzla
-----------------

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
  * `GMP >= v6.1 (GNU Multi-Precision arithmetic library) <https://gmplib.org>`_
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


Cross Compiling for Windows
---------------------------

Cross compiling Bitwuzla with Mingw-w64 can be done as follows:

.. code:: bash

  # Clone Bitwuzla repository
  git clone https://github.com/bitwuzla/bitwuzla
  cd bitwuzla

  # Configure Bitwuzla release build
  ./configure.py --win64

  # Build and install
  cd build && ninja


* **Required Dependencies**

  * `mingw-w64 <https://www.mingw-w64.org/>`_


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

