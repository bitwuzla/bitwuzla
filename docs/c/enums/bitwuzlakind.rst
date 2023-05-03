BitwuzlaKind
------------

The kind of a :cpp:struct:`BitwuzlaTerm`.

Terms of a given kind are created via :cpp:func:`bitwuzla_mk_term()`,
:cpp:func:`bitwuzla_mk_term1()`, :cpp:func:`bitwuzla_mk_term2()`,
:cpp:func:`bitwuzla_mk_term3()`, :cpp:func:`bitwuzla_mk_term1_indexed1()`,
:cpp:func:`bitwuzla_mk_term1_indexed2()`,
:cpp:func:`bitwuzla_mk_term2_indexed1()`, and
:cpp:func:`bitwuzla_mk_term1_indexed2()`.

The kind of a term can be queried via :cpp:func:`bitwuzla_term_get_kind()`.
The string representation of a term kind can be queried via
:cpp:func:`bitwuzla_term_to_string()`, and printed to a given file
via :cpp:func:`bitwuzla_term_print()`.

----

- enum :cpp:enum:`BitwuzlaKind`
- :cpp:func:`bitwuzla_kind_to_string()`

----

.. doxygenenum:: BitwuzlaKind
    :project: Bitwuzla_c

----

.. doxygenfunction:: bitwuzla_kind_to_string
    :project: Bitwuzla_c
