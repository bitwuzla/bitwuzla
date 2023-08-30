C API Documentation
============================

.. toctree::
   :maxdepth: 1

   interface
   options
   Term Kinds <enums/bitwuzlakind>
   sort_creation
   term_creation

.. contents::
   :local:

Quickstart
----------

First, create a :cpp:struct:`BitwuzlaOptions` instance:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 19

This instance can be configured via :cpp:func:`bitwuzla_set_option()`.  
For example, to enable model generation
(SMT-LIB: :code:`(set-option :produce-models true)`):

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 21

Some options have modes, which can be configured via the string representation
of their modes. For example, to enable CaDiCaL as back end SAT solver (this
is for illustration purposes only, CaDiCaL is configured by default):

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 26

For more details on available options, see :doc:`c/options`.

Then, create a :cpp:struct:`Bitwuzla` instance (configuration options are
now frozen and cannot be changed for this instance):

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 28

Next, you will want to create some expressions and assert formulas.
For example, consider the following SMT-LIB input:

.. literalinclude:: ../../examples/smt2/quickstart.smt2
     :language: smtlib

This input is created and asserted as follows:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 18-85

Alternatively, you can parse an input file in BTOR2 format :cite:`btor2` or
SMT-LIB v2 format :cite:`smtlib2` by creating a parser via
:cpp:func:`bitwuzla_parser_new()` and then parsing the input file via
:cpp:func:`bitwuzla_parser_parse()`.

.. note::

  The input parser creates a :cpp:struct:`Bitwuzla` instance, which can be
  configured via the :cpp:struct:`BitwuzlaOptions` instance passed into the
  parser. This Bitwuzla instance can be retrieved via
  :cpp:func:`bitwuzla_parser_get_bitwuzla()`.

For example, to parse an example file `examples/smt2/quickstart.smt2` in SMT-LIB format:

.. literalinclude:: ../../examples/c/parse.c
     :language: c
     :lines: 19-44

.. note::
  If the input is given in SMT-LIB format, commands like :code:`check-sat`
  or :code:`get-value` will be executed while parsing if argument `parse_only`
  is passed into :cpp:func:`bitwuzla_parser_parse()` as :code:`true`.

After parsing an input file and asserting formulas,
satisfiability can be determined via :cpp:func:`bitwuzla_check_sat()`.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 87-88

Formulas can also be assumed via :cpp:func:`bitwuzla_check_sat_assuming()`.

If the formula is satisfiable and model generation has been enabled, the
resulting model can be printed via :cpp:func:`bitwuzla_get_value()` and
:cpp:func:`bitwuzla_term_to_string()`. An example implementation illustrating
how to print the current model via declared symbols (in this case :code:`x`,
:code:`y`, :code:`f` and :code:`a`) is below:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 96-142

This will output a possible model, in this case:

.. code-block:: smtlib

  (
    (define-fun x () (_ BitVec 8) #b10011111)
    (define-fun y () (_ BitVec 8) #b11111111)
    (define-fun f ((@bzla.var_74 (_ BitVec 8)) (@bzla.var_75 (_ BitVec 4))) (_ BitVec 8) (ite (and (= @bzla.var_74 #b10011111) (= @bzla.var_75 #b0011)) #b11111111 #b00000000))
    (define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111))
  )


Alternatively, it is possible to query the value of terms as assignment
string via :cpp:func:`bitwuzla_term_value_get_str()`, or as a term via
:cpp:func:`bitwuzla_get_value()`.

Additionally, for floating-point values,
:cpp:func:`bitwuzla_term_value_get_fp_ieee` allows to retrieve the assignment
split into assignment strings for the sign bit, the exponent and the
significand.
For Boolean and :code:`RoundingMode` values,
:cpp:func:`bitwuzla_term_value_get_bool()` and
:cpp:func:`bitwuzla_term_value_get_rm()` allow the values as :code:`bool` and
:cpp:enum:`BitwuzlaRoundingMode`, respectively.

In our case, we can query the assignments of :code:`x` and :code:`y`, both
bit-vector terms, as binary strings:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 147-152

This will print:

.. code-block::

  value of x: 10011111
  value of y: 11111111

The value of :code:`f` (a function term) and :code:`a` (an array term), on the
other hand, cannot be represented with a simple type. Thus, function values are
given as :cpp:enum:`BitwuzlaKind.LAMBDA <BitwuzlaKind::LAMBDA>`, and array
values are given as
:cpp:enum:`BitwuzlaKind.ARRAY_STORE <BitwuzlaKind::ARRAY_STORE>`.
We can retrieve an SMT-LIB2 string representation of the values via
:cpp:func:`bitwuzla_term_to_string()`:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 154-162

This will print:

.. code-block::

   to_string representation of value of f:
   (lambda ((@bzla.var_74 (_ BitVec 8))) (lambda ((@bzla.var_75 (_ BitVec 4))) (ite (and (= @bzla.var_74 #b10011111) (= @bzla.var_75 #b0011)) #b11111111 #b00000000)))

   to_string representation of value of a:
   (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111)

Note that the string representation of values representable as simple type
(bit-vectors, boolean, floating-point, rounding mode) are given as pure
value string (in the given number format) via
:cpp:func:`bitwuzla_term_value_get_str()`.
Their string representation retrieved via :cpp:func:`bitwuzla_term_to_string()`,
however, is given in SMT-LIB2 format. For example,

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 168-171

This will print:

.. code-block::

   to_string representation of value of x: #b10011111
   to_string representation of value of y: #b11111111


It is also possible to query the model value of expressions that do not
occur in the input formula:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 175-178

This will print:

.. code-block::

  value of v = x * x: 11000001

Finally, we delete the Bitwuzla and Bitwuzla options instance.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 181-182


Examples
--------

| All examples can be found in directory `examples <https://github.com/bitwuzla/bitwuzla/tree/main/examples>`_.
| For instructions on how to build these examples, see `examples/README.md <https://github.com/bitwuzla/bitwuzla/tree/main/examples/README.md>`_.

Quickstart Example
^^^^^^^^^^^^^^^^^^^

| The example used in the :ref:`c/api:quickstart` guide.
| The SMT-LIB input for this example can be found at `examples/smt2/quickstart.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/quickstart.smt2>`_.
| The source code for this example can be found at `examples/c/quickstart.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/quickstart.c>`_.

.. tabbed-examples::
  ../../examples/c/quickstart.c
  ../../examples/cpp/quickstart.cpp
  ../../examples/python/quickstart.py
  ../../examples/smt2/quickstart.smt2

Options Example
^^^^^^^^^^^^^^^

| An example for how to set and get options.
| The SMT-LIB input for this example can be found at `examples/smt2/options.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/options.smt2>`_.
| The source code for this example can be found at `examples/c/options.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/options.c>`_.

.. tabbed-examples::
  ../../examples/c/options.c
  ../../examples/cpp/options.cpp
  ../../examples/python/options.py
  ../../examples/smt2/options.smt2

Option Info Example
^^^^^^^^^^^^^^^^^^^

| An example for how to get information about options via :cpp:struct:`BitwuzlaOptionInfo`.
| The source code for this example can be found at `examples/c/option_info.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/option_info.c>`_.

.. tabbed-examples::
  ../../examples/c/option_info.c
  ../../examples/cpp/option_info.cpp
  ../../examples/python/option_info.py

Incremental Example with push and pop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| An incremental example with :code:`push` and :code:`pop`.
| The SMT-LIB input for this example can be found at `examples/smt2/pushpop.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/pushpop.smt2>`_.
| The source code for this example can be found at `examples/c/pushpop.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/pushpop.c>`_.

.. tabbed-examples::
  ../../examples/c/pushpop.c
  ../../examples/cpp/pushpop.cpp
  ../../examples/python/pushpop.py
  ../../examples/smt2/pushpop.smt2

Incremental Example with check-sat-assuming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`check-sat-assuming`.
| The SMT-LIB input for this example can be found at `examples/smt2/checksatassuming.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/checksatassuming.smt2>`_.
| The source code for this example can be found at `examples/c/checksatassuming.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/checksatassuming.c>`_.

.. tabbed-examples::
  ../../examples/c/checksatassuming.c
  ../../examples/cpp/checksatassuming.cpp
  ../../examples/python/checksatassuming.py
  ../../examples/smt2/checksatassuming.smt2

Unsat Core Example
^^^^^^^^^^^^^^^^^^

This example shows how to extract an unsat core.
It creates bit-vector and floating-point terms and further illustrates how to
create lambda terms (:code:`define-fun`).

| The SMT-LIB input for this example can be found at `examples/smt2/unsatcore.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatcore.smt2>`_.
| The source code for this example can be found at `examples/c/unsatcore.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/unsatcore.c>`_.


.. tabbed-examples::
  ../../examples/c/unsatcore.c
  ../../examples/cpp/unsatcore.cpp
  ../../examples/python/unsatcore.py
  ../../examples/smt2/unsatcore.smt2

Unsat Assumptions Example
^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`get-unsat-assumptions`.
| The SMT-LIB input for this example can be found at `examples/smt2/unsatassumptions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatassumptions.smt2>`_.
| The source code for this example can be found at `examples/c/unsatassumptions.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/unsatassumptions.c>`_.


.. tabbed-examples::
   ../../examples/c/unsatassumptions.c
   ../../examples/cpp/unsatassumptions.cpp
   ../../examples/python/unsatassumptions.py
   ../../examples/smt2/unsatassumptions.smt2

Reset Example
^^^^^^^^^^^^^

| This example shows how to reset the solver instance (SMT-LIB command :code:`reset`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset.smt2>`_.
| The source code for this example can be found at `examples/c/reset.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/reset.c>`_.


.. tabbed-examples::
   ../../examples/c/reset.c
   ../../examples/cpp/reset.cpp
   ../../examples/python/reset.py
   ../../examples/smt2/reset.smt2

Reset Assertions Example
^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to reset the currently asserted formulas of a solver instance (SMT-LIB command :code:`reset-assertions`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset_assertions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset_assertions.smt2>`_.
| The source code for this example can be found at `examples/c/reset_assertions.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/reset_assertions.c>`_.


.. tabbed-examples::
   ../../examples/c/reset_assertions.c
   ../../examples/cpp/reset_assertions.cpp
   ../../examples/python/reset_assertions.py
   ../../examples/smt2/reset_assertions.smt2

Parsing Example
^^^^^^^^^^^^^^^

| This example shows how to parse an input file via the API.
| The source code for this example can be found at `examples/c/parse.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/parse.c>`_.


.. tabbed-examples::
   ../../examples/c/parse.c
   ../../examples/cpp/parse.cpp
   ../../examples/python/parse.py

Printing Example
^^^^^^^^^^^^^^^^

| This example shows how to print sorts, terms and formulas via the API.
| The source code for this example can be found at `examples/c/print.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/print.c>`_.


.. tabbed-examples::
   ../../examples/c/print.c
   ../../examples/cpp/print.cpp
   ../../examples/python/print.py

Termination Callback Example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to configure a termination callback.
| The source code for this example can be found at `examples/c/terminator.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/terminator.c>`_.


.. tabbed-examples::
   ../../examples/c/terminator.c
   ../../examples/cpp/terminator.cpp
   ../../examples/python/terminator.py
