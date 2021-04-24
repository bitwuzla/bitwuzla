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

This instance can be configured via :code:`bitwuzzla_set_option()`.  
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
  ; 0 < x <= 100
  (assert (and (bvugt x (_ bv0 8)) (bvule x (_ bv100 8))))
  ; 0 < y <= 100
  (assert (and (bvugt y (_ bv0 8)) (bvule y (_ bv100 8))))
  ; x * y < 100
  (assert (bvult (bvmul x y) (_ bv100 8)))

This input is created and asserted as follows:

.. code-block:: c

  BitwuzlaSort *bv8 = bitwuzla_mk_bv_sort(bzla, 8);

  BitwuzlaTerm *x = bitwuzla_mk_const(bzla, bv8, "x");
  BitwuzlaTerm *y = bitwuzla_mk_const(bzla, bv8, "y");

  BitwuzlaTerm *zero    = bitwuzla_mk_bv_zero(bzla, bv8);
  BitwuzlaTerm *hundred = bitwuzla_mk_bv_value_uint64(bzla, bv8, 100);

  // 0 < x <= 100
  bitwuzla_assert(bzla,
    bitwuzla_mk_term2(bzla, BITWUZLA_KIND_AND,
      bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_UGT, x, zero),
      bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ULE, x, hundred),
    ));
  // 0 < y <= 100
  bitwuzla_assert(bzla,
    bitwuzla_mk_term2(bzla, BITWUZLA_KIND_AND,
      bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_UGT, y, zero),
      bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ULE, y, hundred),
    ));
  // x * y < 100
  bitwuzla_assert(bzla,
    bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ULT,
      bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_MUL, x, y),
      hundred
    ));

.. note::
  Bitwuzla does not distinguish between sort Boolean and a bit-vector sort of
  size 1. Internally, a Boolean sort is represented as a bit-vector sort of
  size 1.

Alternatively, you can parse an input file in BTOR format :cite:`btor`,
BTOR2 format :cite:`btor2` or SMT-LIB v2 format :cite:`smtlib2` via
:code:`bitwuzla_parse()` (if the format can be auto-detected) or
:code:`bitwuzla_parse_format()` (which requires to specify the input format).
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

If incremental usage is enabled (option :code:`BITWUZLA_OPT_INCREMENTAL`),
formulas can also be assumed via :code:`bitwuzla_assume()`.
After parsing an input file and/or asserting and assuming formulas,
satisfiability can be determined via :code:`bitwuzla_check_sat()`.

.. code-block:: c

  BitwuzlaResult result = bitwuzla_check_sat(bzla);

.. note::
  To simulate SMT-LIB's :code:`check-sat-assuming`, first add assumptions
  via :code:`bitwuzla_assume()`, and then call :code:`bitwuzla_check_sat()`.
  Assumptions are cleared after a call to :code:`bitwuzla_check_sat()`.

If the formula is satisfiable and model generation has been enabled, the
resulting model can be printed via :code:`bitwuzla_print_model()`.

.. code-block:: c

  bitwuzla_print_model(bzla, stdout);

This will output a possible model (default: in SMT-LIB format, configurable
via option :code:`BITWUZLA_OPT_OUTPUT_FORMAT`) as follows:

.. code-block:: smtlib

  (
    (define-fun x () (_ BitVec 8) #b01100100)
    (define-fun y () (_ BitVec 8) #b01100100)
  )


Alternatively, it is possible to query the value of expressions via
:code:`bitwuzla_get_value()`.

.. code-block:: c

  BitwuzlaTerm *v = bitwuzla_get_value(bzla,
      bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_MUL, x, y));

.. todo::

  * What to do with terms retrieved by get_value?
  * unsat cores
  * unsat assumptions
  * push/pop
  * function references as links



Examples
--------
