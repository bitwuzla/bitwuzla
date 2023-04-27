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

First, create a :cpp:struct:`BitwuzlaOptions` instance:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 9

This instance can be configured via :cpp:func:`bitwuzla_set_option()`.  
For example, to enable model generation
(SMT-LIB: :code:`(set-option :produce-models true)`):

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 11

Some options have modes, which can be configured via the string representation
of their modes. For example, to enable CaDiCaL as back end SAT solver (this
is for illustration purposes only, CaDiCaL is configured by default):

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 16

For more details on available options, see :ref:`c/options:options`.

Then, create a :cpp:struct:`Bitwuzla` instance (configuration options are
now frozen and cannot be changed for this instance):

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 18

Next, you will want to create some expressions and assert formulas.
For example, consider the following SMT-LIB input:

.. literalinclude:: ../../examples/smt2/quickstart.smt2
     :language: smtlib

This input is created and asserted as follows:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 8-75

Alternatively, you can parse an input file in BTOR2 format :cite:`btor2` or
SMT-LIB v2 format :cite:`smtlib2` by creating a parser via
:cpp:func:`bitwuzla_parser_new()` and then parsing the input file via
:cpp:func:`bitwuzla_parser_parse()`.
Note that the input parser creates a Bitwuzla instance, which can be
configured via the :cpp:struct:`BitwuzlaOptions` instances passed into the
parser. This Bitwuzla instance can be retrieved via
:cpp:func:`bitwuzla_parser_get_bitwuzla()`.

For example, to parse an example file `examples/smt2/quickstart.smt2` in SMT-LIB format:

.. literalinclude:: ../../examples/c/parse.c
     :language: c
     :lines: 9-26

.. note::
  If the input is given in SMT-LIB format, commands like :code:`check-sat`
  or :code:`get-value` will be executed while parsing if argument `parse_only`
  is passed into :cpp:func:`bitwuzla_parser_parse()` as true.

After parsing an input file and asserting formulas,
satisfiability can be determined via :cpp:func:`bitwuzla_check_sat()`.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 77-78

If incremental usage is enabled (option
:cpp:enum:`BitwuzlaOption.BITWUZLA_OPT_INCREMENTAL <BitwuzlaOption::BITWUZLA_OPT_INCREMENTAL>`),
formulas can also be assumed via :cpp:func:`bitwuzla_check_sat_assuming()`.

If the formula is satisfiable and model generation has been enabled, the
resulting model can be printed via :cpp:func:`bitwuzla_get_value()` and
:cpp:func:`bitwuzla_term_to_string()`. An example implementation to print
the model of declared symbols, in this case `x`, `y`, `f` and `a`, is below:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 86-135

This will output a possible model, in this case:

.. code-block:: smtlib

  (
    (define-fun x () (_ BitVec 8) #b10011111)
    (define-fun y () (_ BitVec 8) #b11111111)
    (define-fun f ((@bzla.var_74 (_ BitVec 8))  (@bzla.var_75 (_ BitVec 4)))  (_ BitVec 8) (ite (and (= @bzla.var_74 #b10011111) (= @bzla.var_75 #b0011)) #b11111111 #b00000000))
    (define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111))
  )



Alternatively, it is possible to query the value of expressions as assignment
string via :cpp:func:`bitwuzla_get_bv_value()`, or as a term via
:cpp:func:`bitwuzla_get_value()`.

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
Note that Bitwuzla requires to first assume formulas (the assumptions in the :code:`check-sat-assuming` list) with :cpp:func:`bitwuzla_assume()` before calling :cpp:func:`bitwuzla_check_sat()`.
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
