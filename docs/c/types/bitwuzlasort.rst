BitwuzlaSort
------------

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

- typedef struct :cpp:struct:`BitwuzlaSort`
- :cpp:func:`bitwuzla_sort_hash()`
- :cpp:func:`bitwuzla_sort_bv_get_size()`
- :cpp:func:`bitwuzla_sort_fp_get_exp_size()`
- :cpp:func:`bitwuzla_sort_fp_get_sig_size()`
- :cpp:func:`bitwuzla_sort_array_get_index()`
- :cpp:func:`bitwuzla_sort_array_get_element()`
- :cpp:func:`bitwuzla_sort_fun_get_domain_sorts()`
- :cpp:func:`bitwuzla_sort_fun_get_codomain()`
- :cpp:func:`bitwuzla_sort_fun_get_arity()`
- :cpp:func:`bitwuzla_sort_get_uninterpreted_symbol()`
- :cpp:func:`bitwuzla_sort_is_equal()`
- :cpp:func:`bitwuzla_sort_is_array()`
- :cpp:func:`bitwuzla_sort_is_bool()`
- :cpp:func:`bitwuzla_sort_is_bv()`
- :cpp:func:`bitwuzla_sort_is_fp()`
- :cpp:func:`bitwuzla_sort_is_fun()`
- :cpp:func:`bitwuzla_sort_is_rm()`
- :cpp:func:`bitwuzla_sort_is_uninterpreted()`
- :cpp:func:`bitwuzla_sort_to_string()`
- :cpp:func:`bitwuzla_sort_print()`

----

.. doxygentypedef:: BitwuzlaSort
    :project: Bitwuzla_c

----

.. doxygengroup:: c_bitwuzlasort
    :project: Bitwuzla_c
    :content-only:
