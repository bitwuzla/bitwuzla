TermManager
-----------

Terms of a given :cpp:enum:`bitwuzla::Kind` are created via
:cpp:func:`TermManager::mk_term()`. A comprehensive documentation of supported
term kinds can be found :doc:`here <enums/kind>`.
For creating terms that represent general and special values of a given sort,
the term manager provides additional functions, see below.

Bitwuzla supports creating array (SMT-LIB: :code:`Array`), Boolean (SMT-LIB:
:code:`Bool`), bit-vector (SMT-LIB: :code:`(_ BitVec n)`), floating-point
(SMT-LIB: :code:`(_ FloatingPoint e s)`), rounding mode (SMT-LIB:
:code:`RoundingMode`), and uninterpreted sorts (SMT-LIB: :code:`declare-sort`).
As for array sorts, this includes nested arrays, i.e., array sorts where the
element sort is an array sort.

.. note::

   Terms and sorts are tied to a specific TermManager instance and can be
   shared across Bitwuzla instances that have the same term manager.

----

- class :cpp:class:`bitwuzla::TermManager`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::TermManager
    :project: Bitwuzla_cpp
    :members:

:code:`}`
