Kind
----

The kind of a :cpp:class:`bitwuzla::Term`.

Terms of a given kind are created via :cpp:func:`bitwuzla::mk_term()`.
The kind of a term can be queried via :cpp:func:`bitwuzla::Term::kind()`.

The string representation of a term kind can be queried via
:cpp:func:`std::string std::to_string(bitwuzla::Kind kind)`, and printed to a
given `ostream` via :cpp:func:`std::ostream& bitwuzla::operator<<(std::ostream&
out, Kind kind)`.

----

- enum :cpp:enum:`bitwuzla::Kind`
- :cpp:func:`std::ostream& bitwuzla::operator<< (std::ostream& out, Kind kind)`
- :cpp:func:`std::string std::to_string(bitwuzla::Kind kind)`

----

:code:`namespace bitwuzla {`

.. doxygenenum:: bitwuzla::Kind
    :project: Bitwuzla_cpp

----

.. doxygenfunction:: bitwuzla::operator<<(std::ostream& out, Kind kind)
    :project: Bitwuzla_cpp

:code:`}`

----

:code:`namespace std {`

.. doxygenfunction:: std::to_string(bitwuzla::Kind kind)
    :project: Bitwuzla_cpp

:code:`}`

