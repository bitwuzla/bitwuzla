Term
----

- class :cpp:class:`bitwuzla::Term`
- struct :cpp:struct:`std::hash\<bitwuzla::Term>`
- :cpp:func:`bool bitwuzla::operator==(const Term& a, const Term& b)`
- :cpp:func:`bool bitwuzla::operator!=(const Term& a, const Term& b)`
- :cpp:func:`std::ostream& bitwuzla::operator<<(std::ostream& out, const Term& term)`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::Term
    :project: Bitwuzla_cpp
    :members:

----

.. doxygenfunction:: bitwuzla::operator==(const Term& a, const Term& b)
    :project: Bitwuzla_cpp

.. doxygenfunction:: bitwuzla::operator!=(const Term& a, const Term& b)
    :project: Bitwuzla_cpp

.. doxygenfunction:: bitwuzla::operator<<(std::ostream& out, const Term& term)
    :project: Bitwuzla_cpp

:code:`}`

----

:code:`namespace std {`

.. doxygenstruct:: std::hash< bitwuzla::Term >
    :project: Bitwuzla_cpp
    :members:

:code:`}`
