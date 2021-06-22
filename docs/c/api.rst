C API Documentation
============================

* :ref:`c/api:quickstart`
* :ref:`c/api:examples`

.. toctree::
  :maxdepth: 2

  options
  kinds
  interface

Quickstart
----------

First, create a :c:struct:`Bitwuzla` instance:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 8

This instance can be configured via :c:func:`bitwuzla_set_option()`.  
For example, to enable model generation
(SMT-LIB: :code:`(set-option :produce-models true)`):

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 10

Some options expect string values rather than integer values, for example,
to enable CryptoMiniSat as back end SAT solver instead of the default
SAT solver CaDiCaL:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 12-14

For more details on available options, see :ref:`c/options:options`.

Next, you will want to create some expressions and assert formulas.
For example, consider the following SMT-LIB input:

.. literalinclude:: ../../examples/smt2/quickstart.smt2
     :language: smtlib

This input is created and asserted as follows:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 7-46

.. note::
  Bitwuzla does not distinguish between sort Boolean and a bit-vector sort of
  size 1. Internally, a Boolean sort is represented as a bit-vector sort of
  size 1.

Alternatively, you can parse an input file in BTOR format :cite:`btor`,
BTOR2 format :cite:`btor2` or SMT-LIB v2 format :cite:`smtlib2` via
:c:func:`bitwuzla_parse()` (if the format can be auto-detected) or
:c:func:`bitwuzla_parse_format()` (which requires to specify the input format).
For example, to parse an input file `example.smt2` in SMT-LIB format:

.. code-block:: c

  char* error_msg;
  BitwuzlaResult status;
  BitwuzlaResult result;

  FILE *fd = fopen("example.smt2", "r");
  result = bitwuzla_parse_format(
    bzla, "smt2", fs, "example.smt2", stdout, &error_msg, &status);

.. note::
  If the input is given in SMT-LIB format, commands like :code:`check-sat`
  or :code:`get-value` will be executed while parsing.

If incremental usage is enabled (option
:c:enum:`BitwuzlaOption.BITWUZLA_OPT_INCREMENTAL`),
formulas can also be assumed via :c:func:`bitwuzla_assume()`.
After parsing an input file and/or asserting and assuming formulas,
satisfiability can be determined via :c:func:`bitwuzla_check_sat()`.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 48-49


.. note::
  To simulate SMT-LIB's :code:`check-sat-assuming`, first add assumptions
  via :c:func:`bitwuzla_assume()`, and then call :c:func:`bitwuzla_check_sat()`.
  Assumptions are cleared after a call to :c:func:`bitwuzla_check_sat()`.

If the formula is satisfiable and model generation has been enabled, the
resulting model can be printed via :c:func:`bitwuzla_print_model()`.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 58-59

This will output a possible model (default: in SMT-LIB format, configurable
via option :c:enum:`BitwuzlaOption.BITWUZLA_OPT_OUTPUT_FORMAT`) as follows:

.. code-block:: smtlib

  (
    (define-fun x () (_ BitVec 8) #b11111111)
    (define-fun y () (_ BitVec 8) #b00011110)
  )


Alternatively, it is possible to query the value of expressions as assignment
string via :c:func:`bitwuzla_get_bv_value()`, or as a term via
:c:func:`bitwuzla_get_value()`.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 62-80

This will print:

.. code-block::

  assignment of x: 11111111
  assignment of y: 00011110

  assignment of x (via bitwuzla_get_value): 11111111
  assignment of y (via bitwuzla_get_value): 00011110


It is also possible to query the model value of expressions that do not
occur in the input formula.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 83-85

This will print:

.. code-block::

  assignment of v = x * x: 00000001

Finally, we delete the Bitwuzla instance.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 88


Examples
--------

| All examples can be found in directory `examples <https://github.com/bitwuzla/bitwuzla/tree/main/examples>`_.
| For instructions on how to build these examples, see `examples/README.md <https://github.com/bitwuzla/bitwuzla/tree/main/examples/README.md>`_.

Quickstart Example
^^^^^^^^^^^^^^^^^^^

The example used in the :ref:`c/api:quickstart` guide.

| The SMT-LIB input for this example can be found at `examples/smt2/quickstart.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/quickstart.smt2>`_.
| The source code for this example can be found at `examples/c/quickstart.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/quickstart.c>`_.

.. tabbed-examples::
  ../../examples/smt2/quickstart.smt2
  ../../examples/c/quickstart.c

Incremental Example with push and pop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An incremental example with :code:`push` and :code:`pop`.

| The SMT-LIB input for this example can be found at `examples/smt2/pushpop.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/pushpop.smt2>`_.
| The source code for this example can be found at `examples/c/pushpop.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/pushpop.c>`_.

.. tabbed-examples::
  ../../examples/smt2/pushpop.smt2
  ../../examples/c/pushpop.c

Incremental Example with check-sat-assuming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This example shows how to implement the example above with
:code:`check-sat-assuming` instead of :code:`push` and :code:`pop`.
Note that Bitwuzla requires to first assume formulas (the assumptions in the :code:`check-sat-assuming` list) with :c:func:`bitwuzla_assume()` before calling :c:func:`bitwuzla_check_sat()`.
All active assumptions are inactivated after the check sat call.

| The SMT-LIB input for this example can be found at `examples/smt2/checksatassuming.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/checksatassuming.smt2>`_.
| The source code for this example can be found at `examples/c/checksatassuming.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/checksatassuming.c>`_.

.. tabbed-examples::
  ../../examples/smt2/checksatassuming.smt2
  ../../examples/c/checksatassuming.c

Unsat Core Example
^^^^^^^^^^^^^^^^^^

This example shows how to extract an unsat core.
It creates bit-vector and floating-point terms and further illustrates how to
create lambda terms (:code:`define-fun`).

| The SMT-LIB input for this example can be found at `examples/smt2/unsatcore.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatcore.smt2>`_.
| The source code for this example can be found at `examples/c/unsatcore.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/unsatcore.c>`_.


.. tabbed-examples::
  ../../examples/smt2/unsatcore.smt2
  ../../examples/c/unsatcore.c

Unsat Assumptions Example
^^^^^^^^^^^^^^^^^^^^^^^^^

This example shows how to implement the example above with
:code:`get-unsat-assumptions`.

| The SMT-LIB input for this example can be found at `examples/smt2/unsatassumptions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatassumptions.smt2>`_.
| The source code for this example can be found at `examples/c/unsatassumptions.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/unsatassumptions.c>`_.


.. tabbed-examples::
   ../../examples/smt2/unsatassumptions.smt2
   ../../examples/c/unsatassumptions.c
