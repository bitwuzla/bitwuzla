BitwuzlaTermManager
===================

.. container:: hide-toctree

  .. toctree::
     :hidden:

- typedef struct :cpp:type:`BitwuzlaTermManager`
- :cpp:func:`bitwuzla_term_manager_new()`
- :cpp:func:`bitwuzla_term_manager_delete()`
- :cpp:func:`bitwuzla_term_manager_release()`

----


.. doxygentypedef:: BitwuzlaTermManager
    :project: Bitwuzla_c

----

.. doxygengroup:: c_bitwuzlatermmanager
    :project: Bitwuzla_c
    :content-only:


Term Creation
-------------

Terms of a given :cpp:enum:`BitwuzlaKind` are created via
:cpp:func:`bitwuzla_mk_term()` (and related `bitwuzla_mk_term*()` functions
provided for convenience). A comprehensive documentation of supported
term kinds can be found :doc:`here </c/enums/bitwuzlakind>`.
For creating terms that represent general and special values of a given sort,
Bitwuzla provides additional functions, see below.

.. note::

   Terms are tied to a specific BitwuzlaTermManager instance and can be shared
   across Bitwuzla instances that have the same term manager.

----

.. doxygengroup:: c_term_creation
    :project: Bitwuzla_c
    :content-only:


Term Substitution
-----------------

.. doxygengroup:: c_term_substitution
    :project: Bitwuzla_c
    :content-only:


Sort Creation
-------------

Bitwuzla supports creating array (SMT-LIB: :code:`Array`), Boolean (SMT-LIB:
:code:`Bool`), bit-vector (SMT-LIB: :code:`(_ BitVec n)`), floating-point
(SMT-LIB: :code:`(_ FloatingPoint e s)`), rounding mode (SMT-LIB:
:code:`RoundingMode`), and uninterpreted sorts (SMT-LIB: :code:`declare-sort`).
As for array sorts, this includes nested arrays, i.e., array sorts where the
element sort is an array sort.

.. note::

   Sorts are tied to a specific BitwuzlaTermManager instance and can be shared
   across Bitwuzla instances that have the same term manager.

----

.. doxygengroup:: c_sort_creation
    :project: Bitwuzla_c
    :content-only:
