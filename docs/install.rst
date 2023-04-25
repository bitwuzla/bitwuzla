Installation
============

Building Bitwuzla
^^^^^^^^^^^^^^^^^

.. code:: bash

  # Download and build Bitwuzla
  git clone https://github.com/bitwuzla/bitwuzla
  cd bitwuzla

  # Configure Bitwuzla release build
  ./configure.py

  # Build and install
  cd build && meson install


*Required Dependencies*
  * `Python >= 3.7 <https://www.python.org>`_
  * `Meson >= 0.64 <https://mesonbuild.com>`_
  * `Ninja <https://ninja-build.org>`_
  * `GMP >= v6.1 (GNU Multi-Precision arithmetic library) <https://gmplib.org>`_
  * `CaDiCaL <https://github.com/arminbiere/cadical>`_
  * `SymFPU <https://github.com/martin-cs/symfpu>`_

.. note::

  If the build system does not find CaDiCaL or SymFPU, it will download
  and build a suitable version itself.


Python Bindings
^^^^^^^^^^^^^^^
.. code:: bash

  git clone https://github.com/bitwuzla/bitwuzla
  cd bitwuzla

  # Build and install Bitwuzla Python bindings
  pip install .


For how to use the Python bindings please refer to the :ref:`python-api`.

*Additional Required Dependencies*
  * `cython <https://pypi.org/project/Cython>`_
  * `meson-python <https://pypi.org/project/meson-python>`_
