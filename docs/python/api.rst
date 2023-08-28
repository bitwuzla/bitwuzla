.. _python-api:

Python API Documentation
=================================

* :ref:`python/api:quickstart`
* :ref:`python/api:examples`

.. toctree::
  :maxdepth: 2

  interface


Quickstart
----------

Examples
--------

| All examples can be found in directory `examples <https://github.com/bitwuzla/bitwuzla/tree/main/examples>`_.
| For instructions on how to build these examples, see `examples/README.md <https://github.com/bitwuzla/bitwuzla/tree/main/examples/README.md>`_.

Quickstart Example
^^^^^^^^^^^^^^^^^^^

| The example used in the :ref:`python/api:quickstart` guide.
| The SMT-LIB input for this example can be found at `examples/smt2/quickstart.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/quickstart.smt2>`_.
| The source code for this example can be found at `examples/python/quickstart.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/quickstart.py>`_.

.. tabbed-examples::
  ../../examples/python/quickstart.py
  ../../examples/cpp/quickstart.cpp
  ../../examples/c/quickstart.c
  ../../examples/smt2/quickstart.smt2

Options Example
^^^^^^^^^^^^^^^

| An example for how to set and get options.
| The source code for this example can be found at `examples/python/options.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/options.py>`_.

.. tabbed-examples::
  ../../examples/python/options.py
  ../../examples/cpp/options.cpp
  ../../examples/c/options.c
  ../../examples/python/options.py

Incremental Example with push and pop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| An incremental example with :code:`push` and :code:`pop`.
| The SMT-LIB input for this example can be found at `examples/smt2/pushpop.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/pushpop.smt2>`_.
| The source code for this example can be found at `examples/python/pushpop.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/pushpop.py>`_.

.. tabbed-examples::
  ../../examples/python/pushpop.py
  ../../examples/cpp/pushpop.cpp
  ../../examples/c/pushpop.c
  ../../examples/smt2/pushpop.smt2

Incremental Example with check-sat-assuming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`check-sat-assuming`.
| The SMT-LIB input for this example can be found at `examples/smt2/checksatassuming.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/checksatassuming.smt2>`_.
| The source code for this example can be found at `examples/python/checksatassuming.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/checksatassuming.py>`_.

.. tabbed-examples::
  ../../examples/python/checksatassuming.py
  ../../examples/cpp/checksatassuming.cpp
  ../../examples/c/checksatassuming.c
  ../../examples/smt2/checksatassuming.smt2

Unsat Core Example
^^^^^^^^^^^^^^^^^^

This example shows how to extract an unsat core.
It creates bit-vector and floating-point terms and further illustrates how to
create lambda terms (:code:`define-fun`).

| The SMT-LIB input for this example can be found at `examples/smt2/unsatcore.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatcore.smt2>`_.
| The source code for this example can be found at `examples/python/unsatcore.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/unsatcore.py>`_.


.. tabbed-examples::
  ../../examples/python/unsatcore.py
  ../../examples/cpp/unsatcore.cpp
  ../../examples/c/unsatcore.c
  ../../examples/smt2/unsatcore.smt2

Unsat Assumptions Example
^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`get-unsat-assumptions`.
| The SMT-LIB input for this example can be found at `examples/smt2/unsatassumptions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatassumptions.smt2>`_.
| The source code for this example can be found at `examples/python/unsatassumptions.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/unsatassumptions.py>`_.


.. tabbed-examples::
   ../../examples/python/unsatassumptions.py
   ../../examples/cpp/unsatassumptions.cpp
   ../../examples/c/unsatassumptions.c
   ../../examples/python/unsatassumptions.py
   ../../examples/smt2/unsatassumptions.smt2

Reset Example
^^^^^^^^^^^^^

| This example shows how to reset the solver instance (SMT-LIB command :code:`reset`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset.smt2>`_.
| The source code for this example can be found at `examples/python/reset.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/reset.py>`_.


.. tabbed-examples::
   ../../examples/python/reset.py
   ../../examples/cpp/reset.cpp
   ../../examples/c/reset.c
   ../../examples/python/reset.py
   ../../examples/smt2/reset.smt2

Reset Assertions Example
^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to reset the currently asserted formulas of a solver instance (SMT-LIB command :code:`reset-assertions`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset_assertions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset_assertions.smt2>`_.
| The source code for this example can be found at `examples/python/reset_assertions.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/reset_assertions.py>`_.


.. tabbed-examples::
   ../../examples/python/reset_assertions.py
   ../../examples/cpp/reset_assertions.cpp
   ../../examples/c/reset_assertions.c
   ../../examples/python/reset_assertions.py
   ../../examples/smt2/reset_assertions.smt2

Printing Example
^^^^^^^^^^^^^^^^

| This example shows how to print sorts, terms and formulas via the API.
| The source code for this example can be found at `examples/python/print.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/print.py>`_.


.. tabbed-examples::
   ../../examples/python/print.py
   ../../examples/c/print.c
   ../../examples/cpp/print.cpp

