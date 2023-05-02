Sort Creation
-------------

Bitwuzla supports creating array (SMT-LIB: :code:`Array`), Boolean (SMT-LIB:
:code:`Bool`), bit-vector (SMT-LIB: :code:`(_ BitVec n)`), floating-point
(SMT-LIB: :code:`(_ FloatingPoint e s)`), rounding mode (SMT-LIB:
:code:`RoundingMode`), and uninterpreted sorts (SMT-LIB: :code:`declare-sort`).
As for array sorts, this includes nested arrays, i.e., array sorts where the
element sort is an array sort.

.. note::

   Sorts are not tied to a specific Bitwuzla instance and can be shared across
   instances.

----

.. doxygengroup:: c_sort_creation
    :project: Bitwuzla_c
    :content-only:
