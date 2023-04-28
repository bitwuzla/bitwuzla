C++ Interface
=============

* :ref:`cpp/interface:classes`
* :ref:`cpp/interface:enums`
* :ref:`cpp/interface:functions`

---------


Classes
-------

Options
^^^^^^^^
.. doxygenclass:: bitwuzla::Options
    :project: Bitwuzla_cpp
    :members:

OptionInfo
^^^^^^^^^^^
.. doxygenstruct:: bitwuzla::OptionInfo
    :project: Bitwuzla_cpp
    :members:

Bitwuzla
^^^^^^^^^
.. doxygenclass:: bitwuzla::Bitwuzla
    :project: Bitwuzla_cpp
    :members:

Sort
^^^^^
.. doxygenclass:: bitwuzla::Sort
    :project: Bitwuzla_cpp
    :members:

Term
^^^^^
.. doxygenclass:: bitwuzla::Term
    :project: Bitwuzla_cpp
    :members:

Parser
^^^^^^
.. doxygenclass:: bitwuzla::parser::Parser
    :project: Bitwuzla_cpp
    :members:

Enums
------

Kind
^^^^^^^^^^^^^^
See :ref:`cpp/kinds:kinds` for more details and examples on how to create terms
of a given kind.

Option
^^^^^^^^^^^^^^
See :ref:`cpp/options:options` for more details and examples on how to set and
get options.

Result
^^^^^^^^^^^^^
.. doxygenenum:: bitwuzla::Result
    :project: Bitwuzla_cpp

RoundingMode
^^^^^^^^^^^^^
.. doxygenenum:: bitwuzla::RoundingMode
    :project: Bitwuzla_cpp

Functions
---------
.. doxygenfile:: bitwuzla.h
    :project: Bitwuzla_cpp
    :sections: func
