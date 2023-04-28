Sort
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
