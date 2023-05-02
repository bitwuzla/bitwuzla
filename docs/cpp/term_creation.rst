Term Creation
-------------

Terms of a given :cpp:enum:`bitwuzla::Kind` are created via
:cpp:func:`bitwuzla::mk_term()`. A comprehensive documentation of supported
term kinds can be found :doc:`here <enums/kind>`.
For creating terms that represent general and special values of a given sort,
Bitwuzla provides additional functions, see below.

.. note::

   Terms are not tied to a specific Bitwuzla instance and can be shared across
   instances.

----

:code:`namespace bitwuzla {`

.. doxygengroup:: cpp_term_creation
    :project: Bitwuzla_cpp
    :content-only:

:code:`}`
