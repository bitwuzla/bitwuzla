BitwuzlaTerm
------------

Terms of a given :cpp:enum:`BitwuzlaKind` are created via
:cpp:func:`bitwuzla_mk_term()` (and related `bitwuzla_mk_term*()` functions
provided for convenience). a comprehensive documentation of supported
term kinds can be found :doc:`here <enums/kind>`.
For creating terms that represent general and special values of a given sort,
Bitwuzla provides additional functions, see below.

.. note::

   Terms are not tied to a specific Bitwuzla instance and can be shared across
   instances.

----

- typedef struct :cpp:struct:`BitwuzlaTerm`
- :cpp:func:`bitwuzla_term_hash()`
- :cpp:func:`bitwuzla_term_get_kind()`
- :cpp:func:`bitwuzla_term_get_children()`
- :cpp:func:`bitwuzla_term_get_indices()`
- :cpp:func:`bitwuzla_term_is_indexed()`
- :cpp:func:`bitwuzla_term_get_sort()`
- :cpp:func:`bitwuzla_term_array_get_index_sort()`
- :cpp:func:`bitwuzla_term_array_get_element_sort()`
- :cpp:func:`bitwuzla_term_fun_get_domain_sorts()`
- :cpp:func:`bitwuzla_term_fun_get_codomain_sort()`
- :cpp:func:`bitwuzla_term_bv_get_size()`
- :cpp:func:`bitwuzla_term_fp_get_exp_size()`
- :cpp:func:`bitwuzla_term_fp_get_sig_size()`
- :cpp:func:`bitwuzla_term_fun_get_arity()`
- :cpp:func:`bitwuzla_term_get_symbol()`
- :cpp:func:`bitwuzla_term_is_equal_sort()`
- :cpp:func:`bitwuzla_term_is_array()`
- :cpp:func:`bitwuzla_term_is_const()`
- :cpp:func:`bitwuzla_term_is_fun()`
- :cpp:func:`bitwuzla_term_is_var()`
- :cpp:func:`bitwuzla_term_is_value()`
- :cpp:func:`bitwuzla_term_is_bv_value()`
- :cpp:func:`bitwuzla_term_is_fp_value()`
- :cpp:func:`bitwuzla_term_is_rm_value()`
- :cpp:func:`bitwuzla_term_is_bool()`
- :cpp:func:`bitwuzla_term_is_bv()`
- :cpp:func:`bitwuzla_term_is_fp()`
- :cpp:func:`bitwuzla_term_is_rm()`
- :cpp:func:`bitwuzla_term_is_uninterpreted()`
- :cpp:func:`bitwuzla_term_is_bv_value_zero()`
- :cpp:func:`bitwuzla_term_is_bv_value_one()`
- :cpp:func:`bitwuzla_term_is_bv_value_ones()`
- :cpp:func:`bitwuzla_term_is_bv_value_min_signed()`
- :cpp:func:`bitwuzla_term_is_bv_value_max_signed()`
- :cpp:func:`bitwuzla_term_is_fp_value_pos_zero()`
- :cpp:func:`bitwuzla_term_is_fp_value_neg_zero()`
- :cpp:func:`bitwuzla_term_is_fp_value_pos_inf()`
- :cpp:func:`bitwuzla_term_is_fp_value_neg_inf()`
- :cpp:func:`bitwuzla_term_is_fp_value_nan()`
- :cpp:func:`bitwuzla_term_is_rm_value_rna()`
- :cpp:func:`bitwuzla_term_is_rm_value_rne()`
- :cpp:func:`bitwuzla_term_is_rm_value_rtn()`
- :cpp:func:`bitwuzla_term_is_rm_value_rtp()`
- :cpp:func:`bitwuzla_term_is_rm_value_rtz()`
- :cpp:func:`bitwuzla_term_value_get_bool()`
- :cpp:func:`bitwuzla_term_value_get_str()`
- :cpp:func:`bitwuzla_term_value_get_fp_ieee()`
- :cpp:func:`bitwuzla_term_value_get_rm()`
- :cpp:func:`bitwuzla_term_to_string()`
- :cpp:func:`bitwuzla_term_print()`

----

.. doxygentypedef:: BitwuzlaTerm
    :project: Bitwuzla_c

----

.. doxygengroup:: c_bitwuzlaterm
    :project: Bitwuzla_c
    :content-only:
