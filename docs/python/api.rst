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
  ../../examples/c/quickstart.c
  ../../examples/cpp/quickstart.cpp
  ../../examples/smt2/quickstart.smt2

Incremental Example with push and pop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| An incremental example with :code:`push` and :code:`pop`.
| The SMT-LIB input for this example can be found at `examples/smt2/pushpop.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/pushpop.smt2>`_.
| The source code for this example can be found at `examples/python/pushpop.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/pushpop.py>`_.

.. tabbed-examples::
  ../../examples/python/pushpop.py
  ../../examples/c/pushpop.c
  ../../examples/cpp/pushpop.cpp
  ../../examples/smt2/pushpop.smt2

Incremental Example with check-sat-assuming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`check-sat-assuming`.
| The SMT-LIB input for this example can be found at `examples/smt2/checksatassuming.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/checksatassuming.smt2>`_.
| The source code for this example can be found at `examples/python/checksatassuming.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/checksatassuming.py>`_.

.. tabbed-examples::
  ../../examples/python/checksatassuming.py
  ../../examples/c/checksatassuming.c
  ../../examples/cpp/checksatassuming.cpp
  ../../examples/smt2/checksatassuming.smt2

Printing Example
^^^^^^^^^^^^^^^^

| This example shows how to print sorts, terms and formulas via the API.
| The source code for this example can be found at `examples/python/print.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/print.py>`_.


.. tabbed-examples::
   ../../examples/python/print.py
   ../../examples/c/print.c
   ../../examples/cpp/print.cpp

