OptionInfo
-----------

The configuration data of an option.

Bitwuzla offers a compact way to retrieve all information about a configuration
option :cpp:enum:`bitwuzla::Option` as a :cpp:struct:`bitwuzla::OptionInfo`
object via :cpp:func:`bitwuzla::OptionInfo::OptionInfo()`.
This object is created per option and can be queried for

- long and short names
- option description
- default value
- minimum/maximum/default values (for numeric options)
- available option modes (for options with modes).

----

- class :cpp:class:`bitwuzla::OptionInfo`

----

:code:`namespace bitwuzla {`

.. doxygenstruct:: bitwuzla::OptionInfo
    :project: Bitwuzla_cpp
    :members:

:code:`}`
