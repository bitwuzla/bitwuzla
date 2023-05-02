Term Creation
-------------

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

.. doxygengroup:: c_term_creation
    :project: Bitwuzla_c
    :content-only:

