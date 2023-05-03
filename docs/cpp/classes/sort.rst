Sort
----

Bitwuzla supports array (SMT-LIB: :code:`Array`), Boolean (SMT-LIB:
:code:`Bool`), bit-vector (SMT-LIB: :code:`(_ BitVec n)`), floating-point
(SMT-LIB: :code:`(_ FloatingPoint e s)`), rounding mode (SMT-LIB:
:code:`RoundingMode`), and uninterpreted sorts (SMT-LIB: :code:`declare-sort`).
As for array sorts, this includes nested arrays, i.e., array sorts where the
element sort is an array sort.

.. note::

   Sorts are not tied to a specific Bitwuzla instance and can be shared across
   instances.

----

- class :cpp:class:`bitwuzla::Sort`
- struct :cpp:struct:`std::hash\<bitwuzla::Sort>`
- :cpp:func:`bool bitwuzla::operator==(const Sort& a, const Sort& b)`
- :cpp:func:`bool bitwuzla::operator!=(const Sort& a, const Sort& b)`
- :cpp:func:`std::ostream& bitwuzla::operator<<(std::ostream& out, const Sort& term)`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::Sort
    :project: Bitwuzla_cpp
    :members:

----

.. doxygenfunction:: bitwuzla::operator==(const Sort& a, const Sort& b)
    :project: Bitwuzla_cpp

.. doxygenfunction:: bitwuzla::operator!=(const Sort& a, const Sort& b)
    :project: Bitwuzla_cpp

.. doxygenfunction:: bitwuzla::operator<<(std::ostream& out, const Sort& term)
    :project: Bitwuzla_cpp

:code:`}`

----

:code:`namespace std {`

.. doxygenstruct:: std::hash< bitwuzla::Sort >
    :project: Bitwuzla_cpp
    :members:

:code:`}`
