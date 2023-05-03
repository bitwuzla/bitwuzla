BitwuzlaOptionInfo
------------------


The configuration data of an option.

Bitwuzla offers a compact way to retrieve all information about a configuration
option :cpp:enum:`BitwuzlaOption` as a :cpp:struct:`BitwuzlaOptionInfo`
object.
This object is created per option via :cpp:func:`bitwuzla_get_option_info()`
and can be queried for

- long and short names
- option description
- default value
- minimum/maximum/default values (for numeric options)
- available option modes (for options with modes).

----

- struct :cpp:struct:`BitwuzlaOptionInfo`
- :cpp:func:`bitwuzla_get_option_info()`

----

.. doxygenstruct:: BitwuzlaOptionInfo
    :project: Bitwuzla_c
    :members:
