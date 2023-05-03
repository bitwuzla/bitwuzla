C++ API Documentation
======================


.. toctree::
   :maxdepth: 1

   interface
   options
   Term Kinds <enums/kind>
   sort_creation
   term_creation

.. contents::
   :local:

Quickstart
----------

First, create a :cpp:class:`bitwuzla::Options` instance:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 12

This instance can be configured via :cpp:func:`bitwuzla::Options::set()`.  
For example, to enable model generation
(SMT-LIB: :code:`(set-option :produce-models true)`):

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 14

Some options have modes, which can be configured via the string representation
of their modes. For example, to enable CaDiCaL as back end SAT solver (this
is for illustration purposes only, CaDiCaL is configured by default):

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 19

For more details on available options, see :doc:`options`.

Then, create a :cpp:struct:`Bitwuzla` instance (configuration options are
now frozen and cannot be changed for this instance):

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 21

Next, you will want to create some expressions and assert formulas.
For example, consider the following SMT-LIB input:

.. literalinclude:: ../../examples/smt2/quickstart.smt2
     :language: smtlib

This input is created and asserted as follows:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 11-66

Alternatively, you can parse an input file in BTOR2 format :cite:`btor2` or
SMT-LIB v2 format :cite:`smtlib2` by creating a parser
:cpp:class:`bitwuzla::parser::Parser` and then parsing the input file via
:cpp:func:`bitwuzla::parser::Parser::parse()`.

.. note::
  The input parser creates a :cpp:class:`Bitwuzla` instance, which can be
  configured via the :cpp:class:`bitwuzla::Options` instance passed into the
  parser. This Bitwuzla instance can be retrieved via
  :cpp:func:`bitwuzla::parser::Parser::bitwuzla()`.

For example, to parse an example file `examples/smt2/quickstart.smt2` in SMT-LIB format:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 12-31

.. note::
  If the input is given in SMT-LIB format, commands like :code:`check-sat`
  or :code:`get-value` will be executed while parsing if argument `parse_only`
  is passed into :cpp:func:`bitwuzla::parser::Parser::parse()` as :code:`true`.

After parsing an input file and asserting formulas, satisfiability can be
determined via :cpp:func:`bitwuzla::Bitwuzla::check_sat()`.

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 68-69

Formulas can also be assumed via passing a vector of assumptions into
:cpp:func:`bitwuzla::Bitwuzla::check_sat()`.

If the formula is satisfiable and model generation has been enabled, the
resulting model can be printed via :cpp:func:`bitwuzla::Bitwuzla::get_value()`
and :cpp:func:`bitwuzla::Term::str()` (or :cpp:func:`bitwuzla::operator<<`).
An example implementation illustrating how to print
the current model via declared symbols (in this case :code:`x`, :code:`y`,
:code:`f` and :code:`a`) is below:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 79-113

This will output a possible model, in this case:

.. code-block:: smtlib

  (
    (define-fun x () (_ BitVec 8) #b10011111)
    (define-fun y () (_ BitVec 8) #b11111111)
    (define-fun f ((@bzla.var_74 (_ BitVec 8))  (@bzla.var_75 (_ BitVec 4))) (_ BitVec 8) (ite (and (= @bzla.var_74 #b10011111) (= @bzla.var_75 #b0011)) #b11111111 #b00000000))
    (define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111))
  )


Alternatively, it is possible to query the value of terms as assignment
string via :cpp:func:`bitwuzla::Term::value()`, or as a term via
:cpp:func:`bitwuzla::Bitwuzla::get_value()`.

Additionally, for floating-point values,
:cpp:func:`bitwuzla_term_value_get_fp_ieee` allows to retrieve the assignment
split into assignment strings for the sign bit, the exponent and the
significand;
for Boolean values as :code:`bool`;
and for :code:`RoundingMode` values as
:cpp:enum:`BitwuzlaRoundingMode`.

In our case, we can query the assignments of :code:`x` and :code:`y`, both
bit-vector terms, as binary strings:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 118-123

This will print:

.. code-block::

  value of x: 10011111
  value of y: 11111111

The value of :code:`f` (a function term) and :code:`a` (an array term), on the
other hand, cannot be represented with a simple type. Thus, function values are
given as :cpp:enum:`bitwuzla::Kind::LAMBDA`, and array values are given as
:cpp:enum:`bitwuzla::Kind::ARRAY_STORE`.
We can retrieve an SMT-LIB2 string representation of the values via
:cpp:func:`bitwuzla::Term::str()` (and :cpp:func:`bitwuzla::operator<<()`:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 125-135

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

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 141-144

This will print:

.. code-block::

   to_string representation of value of x: #b10011111
   to_string representation of value of y: #b11111111


It is also possible to query the model value of expressions that do not
occur in the input formula:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :lines: 148-149

This will print:

.. code-block::

  value of v = x * x: 11000001


Examples
--------

| All examples can be found in directory `examples <https://github.com/bitwuzla/bitwuzla/tree/main/examples>`_.
| For instructions on how to build these examples, see `examples/README.md <https://github.com/bitwuzla/bitwuzla/tree/main/examples/README.md>`_.

Quickstart Example
^^^^^^^^^^^^^^^^^^^

| The example used in the :ref:`cpp/api:quickstart` guide.
| The SMT-LIB input for this example can be found at `examples/smt2/quickstart.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/quickstart.smt2>`_.
| The source code for this example can be found at `examples/cpp/quickstart.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/quickstart.cpp>`_.

.. tabbed-examples::
  ../../examples/smt2/quickstart.smt2
  ../../examples/cpp/quickstart.cpp

Incremental Example with push and pop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| An incremental example with :code:`push` and :code:`pop`.
| The SMT-LIB input for this example can be found at `examples/smt2/pushpop.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/pushpop.smt2>`_.
| The source code for this example can be found at `examples/cpp/pushpop.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/pushpop.cpp>`_.

.. tabbed-examples::
  ../../examples/smt2/pushpop.smt2
  ../../examples/cpp/pushpop.cpp

Incremental Example with check-sat-assuming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`check-sat-assuming`.
| The SMT-LIB input for this example can be found at `examples/smt2/checksatassuming.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/checksatassuming.smt2>`_.
| The source code for this example can be found at `examples/cpp/checksatassuming.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/checksatassuming.cpp>`_.

.. tabbed-examples::
  ../../examples/smt2/checksatassuming.smt2
  ../../examples/cpp/checksatassuming.cpp

Unsat Core Example
^^^^^^^^^^^^^^^^^^

This example shows how to extract an unsat core.
It creates bit-vector and floating-point terms and further illustrates how to
create lambda terms (:code:`define-fun`).

| The SMT-LIB input for this example can be found at `examples/smt2/unsatcore.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatcore.smt2>`_.
| The source code for this example can be found at `examples/cpp/unsatcore.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/unsatcore.cpp>`_.


.. tabbed-examples::
  ../../examples/smt2/unsatcore.smt2
  ../../examples/cpp/unsatcore.cpp

Unsat Assumptions Example
^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`get-unsat-assumptions`.
| The SMT-LIB input for this example can be found at `examples/smt2/unsatassumptions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatassumptions.smt2>`_.
| The source code for this example can be found at `examples/cpp/unsatassumptions.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/unsatassumptions.cpp>`_.


.. tabbed-examples::
   ../../examples/smt2/unsatassumptions.smt2
   ../../examples/cpp/unsatassumptions.cpp

Parsing Example
^^^^^^^^^^^^^^^

| This example shows how to parse an input file via the API.
| The source code for this example can be found at `examples/cpp/parse.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/parse.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/parse.cpp

Termination Callback Example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to configure a termination callback.
| The source code for this example can be found at `examples/cpp/terminator.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/terminator.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/terminator.cpp
