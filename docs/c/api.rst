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

First, create a Bitwuzla instance:

.. code-block:: c

  Bitwuzla *bzla = bitwuzla_new();

This instance can be configured via :c:func:`bitwuzla_set_option()`.  
For example, to enable model generation
(SMT-LIB: :code:`(set-option :produce-models true)`):

.. code-block:: c

  bitwuzla_set_option(bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);

Some options expect string values rather than integer values, for example,
to enable CryptoMiniSat as back end SAT solver instead of the default
SAT solver CaDiCaL:

.. code-block:: c

  bitwuzla_set_option_str(bzla, BITWUZLA_OPT_SAT_ENGINE, "cms");

For more details on available options, see :ref:`c/options:options`.

Next, you will want to create some expressions and assert formulas.
For example, consider the following SMT-LIB input:

.. code-block:: smtlib

  (declare-const x (_ BitVec 8))
  (declare-const y (_ BitVec 8))
  (assert
      (distinct
          ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
          ((_ extract 3 0) (bvashr x (_ bv1 8)))

This input is created and asserted as follows:

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 7-44

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

If incremental usage is enabled (option :c:func:`bitwuzla_OPT_INCREMENTAL`),
formulas can also be assumed via :c:func:`bitwuzla_assume()`.
After parsing an input file and/or asserting and assuming formulas,
satisfiability can be determined via :c:func:`bitwuzla_check_sat()`.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 46-47


.. note::
  To simulate SMT-LIB's :code:`check-sat-assuming`, first add assumptions
  via :c:func:`bitwuzla_assume()`, and then call :c:func:`bitwuzla_check_sat()`.
  Assumptions are cleared after a call to :c:func:`bitwuzla_check_sat()`.

If the formula is satisfiable and model generation has been enabled, the
resulting model can be printed via :c:func:`bitwuzla_print_model()`.

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
     :lines: 54-55

This will output a possible model (default: in SMT-LIB format, configurable
via option :c:func:`bitwuzla_OPT_OUTPUT_FORMAT`) as follows:

.. code-block:: smtlib

  (
    (define-fun x () (_ BitVec 8) #b11111111)
    (define-fun y () (_ BitVec 8) #b00000000)
  )


Alternatively, it is possible to query the value of expressions via
:c:func:`bitwuzla_get_value()`.

.. code-block:: c

  BitwuzlaTerm *v = bitwuzla_get_value(bzla,
      bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_MUL, x, y));

.. todo::

  * What to do with terms retrieved by get_value?
  * unsat cores
  * unsat assumptions
  * push/pop


Examples
--------

All examples can be found in directory
`examples <https://github.com/bitwuzla/bitwuzla/tree/main/examples>`_.
For instructions on how to build these examples, see
`examples/README.md <https://github.com/bitwuzla/bitwuzla/tree/main/examples/README.md>`_.

Quickstart example:
^^^^^^^^^^^^^^^^^^^

.. literalinclude:: ../../examples/c/quickstart.c
     :language: c
