Boolector Python API documentation
==================================

.. _Boolector: https://boolector.github.io
.. _BTOR: http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf
.. _SMT-LIB v1: http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf
.. _SMT-LIB v2: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf

Interface
---------

.. toctree::
    :maxdepth: 1

    Python interface <boolector>


Quickstart
----------


  First, create a Boolector instance: ::
    
    bzla = Boolector() 

  You can configure this instance via :func:`~pyboolector.Boolector.Set_opt`.
  E.g., if you want to enable model generation: ::
   
    bzla.Set_opt(BZLA_OPT_MODEL_GEN, 1)
  
  For a detailed description of all configurable options, see
  :func:`~pyboolector.Boolector.Set_opt`.

  Next you can either parse an input file, and/or generate expressions to 
  be either asserted via :func:`~pyboolector.Boolector.Assert`, or, 
  if incremental usage is enabled,
  assumed via :func:`~pyboolector.Boolector.Assume` (analogously to MiniSAT). 
  Note that Boolector's internal design is motivated by hardware design,
  hence we do not distinguish between type 'Boolean' and type 'bit vector
  of length 1'. 

  E.g., if you want to parse an input file "example.btor", 
  use :func:`~pyboolector.Boolector.Parse`: ::
  
    (result, status, error_msg) = bzla.Parse("example.btor")
  
  Incremental usage is not enabled, hence, if the parser does not encounter
  an error, it returns :data:`~pyboolector.Boolector.UNKNOWN` 
  (for a more detailed description of the parsers return values,
  see :func:`~pyboolector.Boolector.Parse`).
  However, if the parser encounters an error, it returns 
  :data:`~pyboolector.Boolector.PARSE_ERROR`, and an explanation of that error is 
  stored in ``error_msg``. If the input file specifies a (known) status
  of the input formula (either satisfiable or unsatisfiable), that status
  is stored in ``status``.

  As an example for generating and asserting expressions via
  :func:`~pyboolector.Boolector.Assert`, consider the following example: ::

    0 < x <= 100, 0 < y <= 100, x * y < 100

  Given the Boolector instance created above, we generate and assert
  the following expressions: ::
  
    x = bzla.Var(8, "x")
    y = bzla.Var(8, "y")

    bzla.Assert(0 < x)
    bzla.Assert(x <= 100)
    bzla.Assert(0 < y)
    bzla.Assert(y <= 100)
    bzla.Assert(x * y < 100)

    umulo = bzla.Umulo(x, y)  # overflow bit of x * y
    bzla.Assert(~umulo)       # do not allow overflows

  After parsing an input file and/or asserting/assuming expressions,
  the satisfiability of the resulting formula can be determined via
  :func:`~pyboolector.Boolector.Sat`.
  If the resulting formula is satisfiable and model generation has been
  enabled via :func:`~pyboolector.Boolector.Set_opt`, you can either
  print the resulting model via :func:`~pyboolector.Boolector.Print_model`,
  or query assignments
  of bit vector and array variables or uninterpreted functions via
  :data:`~pyboolector.BoolectorNode.assignment`. 
  Note that querying assignments is not limited to variables---you can query 
  the assignment of any arbitrary expression.
 
  E.g., given the example above, we first determine if the formula is
  satisfiable via :func:`~pyboolector.Boolector.Sat` (which it is): ::
  
   result = bzla.Sat()
  
  Now you can either query the assignments of variables ``x`` and ``y`` ::

    print(x.assignment)  # prints: 00000100
    print(y.assignment)  # prints: 00010101
    print("{} {}".format(x.symbol, x.assignment))  # prints: x 00000100
    print("{} {}".format(y.symbol, y.assignment))  # prints: y 00010101 

  or print the resulting model via :func:`~pyboolector.Boolector.Print_model`.
  Boolector supports printing models in its own format ("btor", the default) 
  or in `SMT-LIB v2`_ format ("smt2"): ::
  
    bzla.Print_model()
  
  A possible model would be: ::
  
    2 00000100 x
    3 00010101 y
  
  which in this case indicates the assignments of bit vector variables 
  ``x`` and ``y``. Note that the first column indicates the id of an input, 
  the second column its assignment, and the third column its name (or symbol)
  if any. 
  In the case that the formula includes arrays as input, their values at a
  certain index are indicated as follows: ::

    4[00] 01 A
  
  where A has id 4 and is an array with index and element bit width of 2, 
  and its value at index 0 is 1.

  Printing the above model in `SMT-LIB v2`_ format: ::

    bzla.print_model (format="smt2")

  A possible model would be: ::

    (model
      (define-fun x () (_ BitVec 8) #b00000100)
      (define-fun y () (_ BitVec 8) #b00010101)
      (define-fun y (
       (y_x0 (_ BitVec 2)))
       (ite (= y_x0 #b00) #b01
         #00))
    )

.. _operator-overloading:

Python Operator Overloading
^^^^^^^^^^^^^^^^^^^^^^^^^^^
  For convenience the Boolector Python API provides the following overloaded
  operators on bit vectors (:class:`~pyboolector.BoolectorBVNode`):

  **Arithmetic operators:** ``+ - * / %`` ::

    x = bzla.Var(32)
    y = bzla.Var(32)

    bvadd  = x + y  # bzla.Add(x, y)
    bvsub  = x - y  # bzla.Sub(x, y)
    bvmul  = x * y  # bzla.Mul(x, y)
    bvudiv = x / y  # bzla.Udiv(x, y)
    bvurem = x % y  # bzla.Urem(x, y)
    bvneg  = -x     # bzla.Neg(x)

  **Bitwise operators:** ``~ & | ^ << >>`` ::

    z = bzla.Var(5)

    bvnot = ~x      # bzla.Not(x)
    bvand = x & y   # bzla.And(x, y)
    bvor  = x | y   # bzla.Or(x, y)
    bvxor = x ^ y   # bzla.Xor(x, y)
    bvshl = x << z  # bzla.Sll(x, z) 
    bvshr = x >> z  # bzla.Srl(x, z) 

  **Comparison operators:** ``< <= == != >= >`` ::

    lt   = x < y   # bzla.Ult(x, y)
    lte  = x <= y  # bzla.Ulte(x, y)
    eq   = x == y  # bzla.Eq(x, y)
    ne   = x != y  # bzla.Ne(x, y)
    ugte = x >= y  # bzla.Ugte(x, y)
    ugt  = x > y   # bzla.Ugt(x, y)

  **Python slices:**
  It is possible to use Python slices on bit vectors (see 
  :func:`~pyboolector.Boolector.Slice`), e.g.: ::

    slice_5_2  = x[5:2]  # bzla.Slice(x, 5, 2)
    slice_5_0  = x[5:]   # bzla.Slice(x, 5, 0)
    slice_31_5 = x[:5]   # bzla.Slice(x, x.width - 1, 5)
    slice_31_0 = x[:]    # bzla.Slice(x, x.width - 1, 0) -- copies variable 'x'

  Further, the API also provides convenient ways to create reads
  (see :func:`~pyboolector.Boolector.Read`) on arrays, and function applications
  (see :func:`~pyboolector.Boolector.Apply`).

  **Reads on arrays:** ::

    a = bzla.Array(8, 32)

    read = a[x]  # bzla.Read(a, x) 

  **Function applications:** ::
  
    bv8 = bzla.BitVecSort(8)
    bv32 = bzla.BitVecSort(32)
    f = bzla.UF(bzla.FunSort([bv32, bv32], bv8))

    app = f(x, y)  # bzla.Apply([x, y], f)


.. _const-conversion:

Automatic Constant Conversion
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                                          
  For almost every method of :class:`~pyboolector.Boolector` that creates nodes,
  instead of passing arguments of the type :class:`~pyboolector.BoolectorNode`,
  the Python API allows to pass constants as arguments.
  The only requirement is that it must be possible to derive the bit width of
  the constant operands from the remaining operands.
  For example, binary operators like :func:`~pyboolector.Boolector.Add`
  operands may be a constant, and its bit width will be derived from the other
  non-constant operand, e.g.: ::

    bzla.Add(x, 42)         # bzla.Add(x, bzla.Const(42, x.width))
    bzla.And(0x2a, x)       # bzla.And(bzla.Const(0x2a, x.width), x)
    bzla.Udiv(0b101010, x)  # bzla.Udiv(bzla.Const(0b101010, x.width), x)
           
  For all shift operations it is possible to define the shift width as
  constant, e.g.: ::

    bzla.Sll(x, 5)  # bzla.Sll(x, bzla.Const(5, math.ceil(math.log(x.width, 2)))) 
    bzla.Ror(x, 5)  # bzla.Ror(x, bzla.Const(5, math.ceil(math.log(x.width, 2)))) 

  For operations on arrays all arguments may be constant (except the array
  itself) since the bit width of the operands can be derived from the array,
  e.g.: ::

    bzla.Read(a, 42)       # bzla.Read(a, bzla.Const(42, a.index_with))
    bzla.Write(a, 42, 10)  # bzla.Write(a, bzla.Const(42, a.index_width), bzla.Const(10, a.width))

  This also applies to the arguments of function applications, which can be
  derived from the function's signature, e.g.: ::

    bzla.Apply([42, 10], f)  # bzla.Apply([bzla.Const(42, ...), bzla.Const(10, ...)], f)

  .. note::
    Automatic constant conversion is not possible for the following operators:
    :func:`~pyboolector.Boolector.Not`,
    :func:`~pyboolector.Boolector.Neg`,
    :func:`~pyboolector.Boolector.Redor`,
    :func:`~pyboolector.Boolector.Redxor`,
    :func:`~pyboolector.Boolector.Redand`,
    :func:`~pyboolector.Boolector.Slice`,
    :func:`~pyboolector.Boolector.Uext`,
    :func:`~pyboolector.Boolector.Sext`,
    :func:`~pyboolector.Boolector.Inc`,
    :func:`~pyboolector.Boolector.Dec`, and
    :func:`~pyboolector.Boolector.Concat`
    as the bit with of the resulting node cannot be determined.

Options
-------
 
  Boolector can be configured either via :func:`~pyboolector.Boolector.Set_opt`, 
  or via environment variables of the form: ::

    BTOR<capitalized option name without '_'>=<value>

  For a list and detailed descriptions of all available options, 
  see :func:`~pyboolector.Boolector.Set_opt`.
 
  E.g., given a Boolector instance ``bzla``, model generation is enabled either 
  via ::
  
    bzla.Set_opt(BZLA_OPT_MODEL_GEN, 1)
  
  or via setting the environment variable ::

    BZLAMODELGEN=1


API Tracing
^^^^^^^^^^^

  API tracing allows to record every call to Boolector's public API. The
  resulting trace can be replayed and the replayed sequence behaves exactly 
  like the original Boolector run.
  This is particularly useful for debugging purposes, as it enables replaying
  erroneous behaviour.
  API tracing can be enabled either via 
  setting the environment variable BZLAAPITRACE=<filename>.
 
  E.g., given a Boolector instance 'bzla', enabling API tracing is done as
  follows: ::
   
    BZLAAPITRACE="error.trace"


Internals
---------

  Boolector internally maintains a directed acyclic graph (DAG) of
  expressions. 
  By asserting an expression, it will be permanently added to the
  formula. 
  Assumptions, in contrast, are cleared after a call to 
  :func:`~pyboolector.Boolector.Sat`.
  You can query assumptions that force a formula to be unsatisfiable
  via :func:`~pyboolector.Boolector.Failed`.

Operators
^^^^^^^^^

  Boolector internally describes expressions by means of a set of base
  operators as documented in BZLA_.
  Boolector's API, however, provides a richer set of operators for
  convenience, where non-base operators are internally rewritten to use
  base operators only.
  E.g., two's complement (:func:`~pyboolector.Boolector.Neg`) is rewritten as 
  one's complement and addition of 1. 
  Note that this behaviour is not influenced by the rewrite level chosen.
 
Rewriting
^^^^^^^^^

  Boolector simplifies expressions and the expression DAG by means of 
  rewriting and supports three so-called rewrite levels.
  Increasing rewrite levels increase the extent of rewriting performed,
  and a rewrite level of 0 is equivalent to disabling rewriting at all.
  Note that Boolector not only simplifies expressions during construction
  of the expression DAG---for each call to \ref boolector_sat,
  various simplification techniques and rewriting phases are initiated.
  You can force Boolector to initiate rewriting and simplify the expression
  DAG via :func:`~pyboolector.Boolector.Simplify`.
  The rewrite level can be configured via :func:`~pyboolector.Boolector.Set_opt`.

Examples
--------

  .. literalinclude:: ../examples/api/python/api_usage_examples.py
