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

First, create a :class:`bitwuzla.Options` instance:

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 18

This instance can be configured via :obj:`bitwuzla.Options.set()`.  
For example, to enable model generation
(SMT-LIB: :code:`(set-option :produce-models true)`):

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 20

Some options have modes, which can be configured via the string representation
of their modes. For example, to enable CaDiCaL as back end SAT solver (this
is for illustration purposes only, CaDiCaL is configured by default):

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 25

For more details on available options, see :doc:`options`.

Then, create a :class:`bitwuzla.Bitwuzla` instance (configuration options are
now frozen and cannot be changed for this instance):

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 27

Next, you will want to create some expressions and assert formulas.
For example, consider the following SMT-LIB input:

.. literalinclude:: ../../examples/smt2/quickstart.smt2
     :language: smtlib

This input is created and asserted as follows:

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 17-72

Alternatively, you can parse an input file in BTOR2 format :cite:`btor2` or
SMT-LIB v2 format :cite:`smtlib2` by creating a parser
:class:`bitwuzla.Parser` and then parsing the input file via
:obj:`bitwuzla.Parser.parse()`.

.. note::
  The input parser creates a :class:`bitwuzla.Bitwuzla` instance, which can be
  configured via the :class:`bitwuzla.Options` instance passed into the
  parser. This Bitwuzla instance can be retrieved via
  :obj:`bitwuzla.Parser.bitwuzla()`.

For example, to parse an example file `examples/smt2/quickstart.smt2` in SMT-LIB format:

.. literalinclude:: ../../examples/python/parse.py
     :language: python
     :lines: 17-35

.. note::
  If the input is given in SMT-LIB format, commands like :code:`check-sat`
  or :code:`get-value` will be executed while parsing if argument `parse_only`
  is passed into :obj:`bitwuzla.Parser.parse()` as :code:`True`.

After parsing an input file and asserting formulas, satisfiability can be
determined via :obj:`bitwuzla.Bitwuzla.check_sat()`.

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 74-75

Formulas can also be assumed via passing a vector of assumptions into
:python:func:`bitwuzla::Bitwuzla::check_sat()`.

If the formula is satisfiable and model generation has been enabled, the
resulting model can be printed via :python:func:`bitwuzla::Bitwuzla::get_value()`
and :python:func:`bitwuzla::Term::str()` (or :cpp:func:`bitwuzla::operator<<`).
An example implementation illustrating how to print
the current model via declared symbols (in this case :code:`x`, :code:`y`,
:code:`f` and :code:`a`) is below:

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 79-101

This will output a possible model, in this case:

.. code-block:: smtlib

  (
    (define-fun x () (_ BitVec 8) #b10011111)
    (define-fun y () (_ BitVec 8) #b11111111)
    (define-fun f ((@bzla.var_74 (_ BitVec 8))  (@bzla.var_75 (_ BitVec 4))) (_ BitVec 8) (ite (and (= @bzla.var_74 #b10011111) (= @bzla.var_75 #b0011)) #b11111111 #b00000000))
    (define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111))
  )


Alternatively, it is possible to query the value of terms as a term via
:obj:`bitwuzla.Bitwuzla.get_value()`; or as assignment via
:obj:`bitwuzla.Term.value()`, which returns the string representation
of bit-vector and floating-point values, the
:class:`bitwuzla.RoundingMode` value for RoundingMode values, and a :code:`bool`
value for Boolean values.

Additionally, for floating-point values,
:obj:`bitwuzla.Term.value()` allows to retrieve the assignment
split into assignment strings for the sign bit, the exponent and the
significand.

In our case, we can query the assignments of :code:`x` and :code:`y`, both
bit-vector terms, as binary strings:

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 109-117

This will print:

.. code-block::

  value of x: 10011111
  value of y: 11111111

The value of :code:`f` (a function term) and :code:`a` (an array term), on the
other hand, cannot be represented with a simple type. Thus, function values are
given as :obj:`bitwuzla.Kind.LAMBDA`, and array values are given as
:obj:`bitwuzla.Kind.ARRAY_STORE`.
We can retrieve an SMT-LIB2 string representation of the values via
:obj:`bitwuzla.Term.str()`.

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 109-117

This will print:

.. code-block::

   str() representation of value of f:
   (lambda ((@bzla.var_74 (_ BitVec 8))) (lambda ((@bzla.var_75 (_ BitVec 4))) (ite (and (= @bzla.var_74 #b10011111) (= @bzla.var_75 #b0011)) #b11111111 #b00000000)))

   str() representation of value of a:
   (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111)

Note that the string representation of values representable as simple type
(bit-vectors, boolean, floating-point, rounding mode) are given as pure
value string (in the given number format) via
:obj:`bitwuzla.Term.value()`.
Their string representation retrieved via :obj:`bitwuzla.Term.str()`,
however, is given in SMT-LIB2 format. For example,

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 123-124

This will print:

.. code-block::

   str() representation of value of x: #b10011111
   str() representation of value of y: #b11111111


It is also possible to query the model value of expressions that do not
occur in the input formula:

.. literalinclude:: ../../examples/python/quickstart.py
     :language: python
     :lines: 129

This will print:

.. code-block::

  value of v = x * x: 11000001
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
  ../../examples/python/quickstart.py
  ../../examples/c/quickstart.c
  ../../examples/smt2/quickstart.smt2

Options Example
^^^^^^^^^^^^^^^

| An example for how to set and get options.
| The SMT-LIB input for this example can be found at `examples/smt2/options.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/options.smt2>`_.
| The source code for this example can be found at `examples/python/options.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/options.py>`_.

.. tabbed-examples::
  ../../examples/python/options.py
  ../../examples/python/options.py
  ../../examples/c/options.c
  ../../examples/smt2/options.smt2

Option Info Example
^^^^^^^^^^^^^^^^^^^

| An example for how to get information about options via :cpp:struct:`BitwuzlaOptionInfo`.
| The source code for this example can be found at `examples/python/option_info.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/option_info.py>`_.

.. tabbed-examples::
  ../../examples/python/option_info.py
  ../../examples/cpp/option_info.cpp
  ../../examples/c/option_info.c

Incremental Example with push and pop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| An incremental example with :code:`push` and :code:`pop`.
| The SMT-LIB input for this example can be found at `examples/smt2/pushpop.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/pushpop.smt2>`_.
| The source code for this example can be found at `examples/python/pushpop.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/pushpop.py>`_.

.. tabbed-examples::
  ../../examples/python/pushpop.py
  ../../examples/python/pushpop.py
  ../../examples/c/pushpop.c
  ../../examples/smt2/pushpop.smt2

Incremental Example with check-sat-assuming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`check-sat-assuming`.
| The SMT-LIB input for this example can be found at `examples/smt2/checksatassuming.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/checksatassuming.smt2>`_.
| The source code for this example can be found at `examples/python/checksatassuming.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/checksatassuming.py>`_.

.. tabbed-examples::
  ../../examples/python/checksatassuming.py
  ../../examples/python/checksatassuming.py
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
  ../../examples/python/unsatcore.py
  ../../examples/c/unsatcore.c
  ../../examples/smt2/unsatcore.smt2

Unsat Assumptions Example
^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`get-unsat-assumptions`.
| The SMT-LIB input for this example can be found at `examples/smt2/unsatassumptions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatassumptions.smt2>`_.
| The source code for this example can be found at `examples/python/unsatassumptions.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/unsatassumptions.py>`_.


.. tabbed-examples::
   ../../examples/python/unsatassumptions.py
   ../../examples/python/unsatassumptions.py
   ../../examples/c/unsatassumptions.c
   ../../examples/smt2/unsatassumptions.smt2

Reset Example
^^^^^^^^^^^^^

| This example shows how to reset the solver instance (SMT-LIB command :code:`reset`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset.smt2>`_.
| The source code for this example can be found at `examples/python/reset.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/reset.py>`_.


.. tabbed-examples::
   ../../examples/python/reset.py
   ../../examples/python/reset.py
   ../../examples/c/reset.c
   ../../examples/smt2/reset.smt2

Reset Assertions Example
^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to reset the currently asserted formulas of a solver instance (SMT-LIB command :code:`reset-assertions`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset_assertions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset_assertions.smt2>`_.
| The source code for this example can be found at `examples/python/reset_assertions.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/reset_assertions.py>`_.


.. tabbed-examples::
   ../../examples/python/reset_assertions.py
   ../../examples/python/reset_assertions.py
   ../../examples/c/reset_assertions.c
   ../../examples/smt2/reset_assertions.smt2

Parsing Example
^^^^^^^^^^^^^^^

| This example shows how to parse an input file via the API.
| The source code for this example can be found at `examples/python/parse.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/parse.py>`_.


.. tabbed-examples::
   ../../examples/python/parse.py
   ../../examples/python/parse.py
   ../../examples/c/parse.c

Printing Example
^^^^^^^^^^^^^^^^

| This example shows how to print sorts, terms and formulas via the API.
| The source code for this example can be found at `examples/python/print.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/print.py>`_.


.. tabbed-examples::
   ../../examples/python/print.py
   ../../examples/python/print.py
   ../../examples/c/print.c

Termination Callback Example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to configure a termination callback.
| The source code for this example can be found at `examples/python/terminator.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/terminator.py>`_.


.. tabbed-examples::
   ../../examples/python/terminator.py
   ../../examples/python/terminator.py
   ../../examples/c/terminator.c
