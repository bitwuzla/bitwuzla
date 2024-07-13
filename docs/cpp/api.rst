C++ API Documentation
======================

The :doc:`C++ API <interface>` of Bitwuzla is its primary API.
This section provides a :ref:`quickstart <cpp/api:quickstart>` guide to give an
introduction on how to use the C++ API and a comprehensive set of
:ref:`examples <cpp/api:examples>` to cover basic and common use cases. A
comprehensive description of the interface is given :doc:`here <interface>`.

----

.. toctree::
   :maxdepth: 1

   interface
   options
   Term Kinds <enums/kind>

.. contents::
   :local:

-----

Quickstart
----------

First, create a :cpp:class:`TermManager` instance that allows us to
create sorts and terms later:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: c
     :start-after: docs-cpp-quickstart-0 start
     :end-before: docs-cpp-quickstart-0 end

Then, create a :cpp:class:`bitwuzla::Options` instance:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-1 start
     :end-before: docs-cpp-quickstart-1 end

This instance can be configured via :cpp:func:`bitwuzla::Options::set()`.  
For example, to enable model generation
(SMT-LIB: :code:`(set-option :produce-models true)`):

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-2 start
     :end-before: docs-cpp-quickstart-2 end

Some options have **modes**, which can be configured via the string
representation of their modes. For example, to enable CaDiCaL as back end SAT
solver (this is for illustration purposes only, CaDiCaL is configured by
default):

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-3 start
     :end-before: docs-cpp-quickstart-3 end

For more details on available options, see :doc:`options`.

Then, create a :cpp:type:`Bitwuzla` **solver** instance with a term manager
and configured options (configuration options are now frozen and cannot be
changed for this instance):

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-4 start
     :end-before: docs-cpp-quickstart-4 end

Next, you will want to **create** some **expressions** via the term manager
`tm` and **assert formulas**.

.. note::

  Sorts and terms can be shared between multiple solver instances as long as
  these solvers use the same term manager.

For example, consider the following SMT-LIB input:

.. literalinclude:: ../../examples/smt2/quickstart.smt2
     :language: smtlib

This input is created and asserted as follows:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-5 start
     :end-before: docs-cpp-quickstart-5 end

Alternatively, you can **parse** an **input file** in BTOR2 format
:cite:`btor2` or SMT-LIB v2 format :cite:`smtlib2` by creating a parser
:cpp:class:`bitwuzla::parser::Parser` and then parsing the input file via
:cpp:func:`bitwuzla::parser::Parser::parse()`.

.. note::
  The input parser creates a :cpp:type:`Bitwuzla` instance, which can be
  configured via the :cpp:class:`bitwuzla::Options` instance passed into the
  parser. This Bitwuzla instance can be retrieved via
  :cpp:func:`bitwuzla::parser::Parser::bitwuzla()`.

For example, to parse an example file `examples/smt2/quickstart.smt2` in SMT-LIB format:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 22-29,31-32,36,86-91

.. note::
  If the input is given in SMT-LIB format, commands like :code:`check-sat`
  or :code:`get-value` will be executed while parsing if argument `parse_only`
  is passed into :cpp:func:`bitwuzla::parser::Parser::parse()` as :code:`true`.

After parsing from an input file, the **parsed assertions** can be retrieved
via :cpp:func:`bitwuzla::Bitwuzla::get_assertions()`:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 38-45

Alternatively, Bitwuzla also supports **parsing from strings** via
:cpp:func:`bitwuzla::parser::Parser::parse()`. The quickstart input above can
be parsed as one huge input string, or any its subsets of commands.

Bitwuzla also allows to **add onto** input parsed from a file.
For example, after parsing in ``examples/smt2/quickstart.smt2``, which is
satisfiable, we add an assertion (which now makes the input formula
unsatisfiable) via parsing from string as follows:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 48

Bitwuzla also supports **parsing terms and sorts from strings** via
:cpp:func:`bitwuzla::parser::Parser::parse_term()` and
:cpp:func:`bitwuzla::parser::Parser::parse_sort()`.

.. note:: Declarations like :code:`declare-const` are commands (not terms) in
          the SMT-LIB language. Commands must be parsed in via
          :cpp:func:`bitwuzla::parser::Parser::parse()`.
          Function :cpp:func:`bitwuzla::parser::Parser::parse_term()` and
          :cpp:func:`bitwuzla::parser::Parser::parse_sort()` only support
          parsing SMT-LIB terms and sorts, respectively.

For example, to **parse** a bit-vector **sort** of size 16 from string and show
that it corresponds to the bit-vector sort of size 16 created via
:cpp:func:`bitwuzla::mk_bv_sort()`:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 58-62

Then, to **declare** Boolean constants :code:`c` and :code:`d` and a bit-vector
constant :code:`b`:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 68,70

These terms can be retrieved via
:cpp:func:`bitwuzla::parser::Parser::parse_term()`:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 71-76

Now, to **parse** in **terms** using these constants via
:cpp:func:`bitwuzla::parser::Parser::parse_term()`:

.. literalinclude:: ../../examples/cpp/parse.cpp
     :language: cpp
     :lines: 77-85

After parsing input and asserting formulas, **satisfiability** can be
determined via :cpp:func:`bitwuzla::Bitwuzla::check_sat()`.

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-6 start
     :end-before: docs-cpp-quickstart-6 end

Formulas can also be **assumed** via passing a vector of assumptions into
:cpp:func:`bitwuzla::Bitwuzla::check_sat()`.

If the formula is satisfiable and **model generation** has been enabled, the
resulting model can be printed via :cpp:func:`bitwuzla::Bitwuzla::get_value()`
and :cpp:func:`bitwuzla::Term::str()` (or :cpp:func:`bitwuzla::operator<<`).
An example implementation illustrating how to print
the current model via declared symbols (in this case :code:`x`, :code:`y`,
:code:`f` and :code:`a`) is below:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-7 start
     :end-before: docs-cpp-quickstart-7 end

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
:cpp:func:`bitwuzla::Term::value()` allows to retrieve the assignment
split into assignment strings for the sign bit, the exponent and the
significand;
for Boolean values as :code:`bool`;
and for :code:`RoundingMode` values as
:cpp:enum:`BitwuzlaRoundingMode`.

In our case, we can query the assignments of :code:`x` and :code:`y`, both
bit-vector terms, as binary strings:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-8 start
     :end-before: docs-cpp-quickstart-8 end

This will print:

.. code-block::

  value of x: 10011111
  value of y: 11111111

The value of :code:`f` (a function term) and :code:`a` (an array term), on the
other hand, cannot be represented with a simple type. Thus, function values are
given as :cpp:enumerator:`bitwuzla::Kind::LAMBDA`, and array values are given as
:cpp:enumerator:`bitwuzla::Kind::ARRAY_STORE`.
We can retrieve an SMT-LIB2 string representation of the values via
:cpp:func:`bitwuzla::Term::str()` (and :cpp:func:`bitwuzla::operator<<()`):

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-9 start
     :end-before: docs-cpp-quickstart-9 end

This will print:

.. code-block::

   str() representation of value of f:
   (lambda ((@bzla.var_74 (_ BitVec 8))) (lambda ((@bzla.var_75 (_ BitVec 4))) (ite (and (= @bzla.var_74 #b10011111) (= @bzla.var_75 #b0011)) #b11111111 #b00000000)))

   str() representation of value of a:
   (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00000000) #b10011111 #b11111111)

Note that the string representation of values representable as simple type
(bit-vectors, boolean, floating-point, rounding mode) are given as pure
value string (in the given number format) via
:cpp:func:`bitwuzla::Term::value()`.
Their string representation retrieved via :cpp:func:`bitwuzla::Term::str()`,
however, is given in SMT-LIB2 format. For example,

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-10 start
     :end-before: docs-cpp-quickstart-10 end

This will print:

.. code-block::

   str() representation of value of x: #b10011111
   str() representation of value of y: #b11111111


It is also possible to query the model value of expressions that do not
occur in the input formula:

.. literalinclude:: ../../examples/cpp/quickstart.cpp
     :language: cpp
     :start-after: docs-cpp-quickstart-11 start
     :end-before: docs-cpp-quickstart-11 end

This will print:

.. code-block::

  value of v = x * x: 11000001

-----

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
  ../../examples/cpp/quickstart.cpp
  ../../examples/c/quickstart.c
  ../../examples/python/quickstart.py
  ../../examples/smt2/quickstart.smt2

Options Example
^^^^^^^^^^^^^^^

| An example for how to set and get options.
| The SMT-LIB input for this example can be found at `examples/smt2/options.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/options.smt2>`_.
| The source code for this example can be found at `examples/cpp/options.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/options.cpp>`_.

.. tabbed-examples::
  ../../examples/cpp/options.cpp
  ../../examples/c/options.c
  ../../examples/python/options.py
  ../../examples/smt2/options.smt2

Option Info Example
^^^^^^^^^^^^^^^^^^^

| An example for how to get information about options via :cpp:class:`OptionInfo`.
| The source code for this example can be found at `examples/cpp/option_info.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/option_info.cpp>`_.

.. tabbed-examples::
  ../../examples/cpp/option_info.cpp
  ../../examples/c/option_info.c
  ../../examples/python/option_info.py

Incremental Example with push and pop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| An incremental example with :code:`push` and :code:`pop`.
| The SMT-LIB input for this example can be found at `examples/smt2/pushpop.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/pushpop.smt2>`_.
| The source code for this example can be found at `examples/cpp/pushpop.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/pushpop.cpp>`_.

.. tabbed-examples::
  ../../examples/cpp/pushpop.cpp
  ../../examples/c/pushpop.c
  ../../examples/python/pushpop.py
  ../../examples/smt2/pushpop.smt2

Incremental Example with check-sat-assuming
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`check-sat-assuming`.
| The SMT-LIB input for this example can be found at `examples/smt2/checksatassuming.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/checksatassuming.smt2>`_.
| The source code for this example can be found at `examples/cpp/checksatassuming.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/checksatassuming.cpp>`_.

.. tabbed-examples::
  ../../examples/cpp/checksatassuming.cpp
  ../../examples/c/checksatassuming.c
  ../../examples/python/checksatassuming.py
  ../../examples/smt2/checksatassuming.smt2

Unsat Core Example
^^^^^^^^^^^^^^^^^^

This example shows how to extract an unsat core.
It creates bit-vector and floating-point terms and further illustrates how to
create lambda terms (:code:`define-fun`).

| The SMT-LIB input for this example can be found at `examples/smt2/unsatcore.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatcore.smt2>`_.
| The source code for this example can be found at `examples/cpp/unsatcore.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/unsatcore.cpp>`_.


.. tabbed-examples::
  ../../examples/cpp/unsatcore.cpp
  ../../examples/c/unsatcore.c
  ../../examples/python/unsatcore.py
  ../../examples/smt2/unsatcore.smt2

Unsat Assumptions Example
^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to implement the example above with :code:`get-unsat-assumptions`.
| The SMT-LIB input for this example can be found at `examples/smt2/unsatassumptions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/unsatassumptions.smt2>`_.
| The source code for this example can be found at `examples/cpp/unsatassumptions.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/unsatassumptions.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/unsatassumptions.cpp
   ../../examples/c/unsatassumptions.c
   ../../examples/python/unsatassumptions.py
   ../../examples/smt2/unsatassumptions.smt2

Reset Example
^^^^^^^^^^^^^

| This example shows how to reset the solver instance (SMT-LIB command :code:`reset`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset.smt2>`_.
| The source code for this example can be found at `examples/cpp/reset.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/reset.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/reset.cpp
   ../../examples/c/reset.c
   ../../examples/python/reset.py
   ../../examples/smt2/reset.smt2

Reset Assertions Example
^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to reset the currently asserted formulas of a solver instance (SMT-LIB command :code:`reset-assertions`).
| The SMT-LIB input for this example can be found at `examples/smt2/reset_assertions.smt2 <https://github.com/bitwuzla/bitwuzla/tree/main/examples/smt2/reset_assertions.smt2>`_.
| The source code for this example can be found at `examples/cpp/reset_assertions.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/reset_assertions.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/reset_assertions.cpp
   ../../examples/c/reset_assertions.c
   ../../examples/python/reset_assertions.py
   ../../examples/smt2/reset_assertions.smt2

Parsing Example
^^^^^^^^^^^^^^^

| This example shows how to parse an input file via the API.
| The source code for this example can be found at `examples/cpp/parse.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/parse.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/parse.cpp
   ../../examples/c/parse.c
   ../../examples/python/parse.py

Printing Example
^^^^^^^^^^^^^^^^

| This example shows how to print sorts, terms and formulas via the API.
| The source code for this example can be found at `examples/cpp/print.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/print.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/print.cpp
   ../../examples/c/print.c
   ../../examples/python/print.py

Termination Callback Example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

| This example shows how to configure a termination callback.
| The source code for this example can be found at `examples/cpp/terminator.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/terminator.cpp>`_.


.. tabbed-examples::
   ../../examples/cpp/terminator.cpp
   ../../examples/c/terminator.c
   ../../examples/python/terminator.py
