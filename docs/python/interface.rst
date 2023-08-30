Python Interface
================

* :ref:`python/interface:classes`

  * :ref:`python/interface:options`
  * :ref:`python/interface:bitwuzla`
  * :ref:`python/interface:sort`
  * :ref:`python/interface:term`

* :ref:`python/interface:functions`

  * :ref:`python/interface:sort creation`
  * :ref:`python/interface:term creation`

    * :ref:`python/interface:values`
    * :ref:`python/interface:special values`

* :ref:`python/interface:enums`

  * :ref:`python/interface:option`
  * :ref:`python/interface:kind`
  * :ref:`python/interface:result`
  * :ref:`python/interface:roundingmode`


Classes
-------

Options
^^^^^^^
.. autoclass:: bitwuzla.Options
   :members:
   :undoc-members:

Bitwuzla
^^^^^^^^
.. autoclass:: bitwuzla.Bitwuzla
   :members:
   :undoc-members:

Sort
^^^^
.. autoclass:: bitwuzla.Sort
   :members:
   :undoc-members:

Term
^^^^
.. autoclass:: bitwuzla.Term
   :members:
   :undoc-members:

Parser
^^^^^^
.. autoclass:: bitwuzla.Parser
   :members:
   :undoc-members:

Functions
---------

Sort Creation
^^^^^^^^^^^^^
.. autofunction:: bitwuzla.mk_bool_sort
.. autofunction:: bitwuzla.mk_bv_sort
.. autofunction:: bitwuzla.mk_array_sort
.. autofunction:: bitwuzla.mk_fun_sort
.. autofunction:: bitwuzla.mk_fp_sort
.. autofunction:: bitwuzla.mk_rm_sort
.. autofunction:: bitwuzla.mk_uninterpreted_sort

Term Creation
^^^^^^^^^^^^^

.. autofunction:: bitwuzla.mk_const
.. autofunction:: bitwuzla.mk_const_array
.. autofunction:: bitwuzla.mk_var
.. autofunction:: bitwuzla.mk_term

Values
""""""
.. autofunction:: bitwuzla.mk_true
.. autofunction:: bitwuzla.mk_false
.. autofunction:: bitwuzla.mk_bv_value
.. autofunction:: bitwuzla.mk_fp_value
.. autofunction:: bitwuzla.mk_rm_value

Special Values
""""""""""""""
.. autofunction:: bitwuzla.mk_bv_ones
.. autofunction:: bitwuzla.mk_bv_min_signed
.. autofunction:: bitwuzla.mk_bv_max_signed
.. autofunction:: bitwuzla.mk_fp_pos_zero
.. autofunction:: bitwuzla.mk_fp_neg_zero
.. autofunction:: bitwuzla.mk_fp_pos_inf
.. autofunction:: bitwuzla.mk_fp_neg_inf
.. autofunction:: bitwuzla.mk_fp_nan

Enums
------

Option
^^^^^^
.. autoclass:: bitwuzla.Option
   :members:
   :undoc-members:

Kind
^^^^
.. autoclass:: bitwuzla.Kind
   :members:
   :undoc-members:

Result
^^^^^^
.. autoclass:: bitwuzla.Result
   :members:
   :undoc-members:

RoundingMode
^^^^^^^^^^^^
.. autoclass:: bitwuzla.RoundingMode
   :members:
   :undoc-members:


