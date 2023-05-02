.. _c_options:

Options
========

A :cpp:struct:`Bitwuzla` instance is created from a configuration
options :cpp:struct:`BitwuzlaOptions` instance. This options instance must
be configured before creating the Bitwuzla instance: **after** the Bitwuzla
instance is created, configuration options are fixed and **cannot** be changed.

Via the C API, **Bitwuzla** distinguishes two kinds of options: Numeric options
(including Boolean options) and options with option modes.
The kind of an option can be queried via
:cpp:func:`bitwuzla_option_is_numeric()`, and
:cpp:func:`bitwuzla_option_is_mode()`.

Boolean and numeric options are configured via
:cpp:func:`bitwuzla_set_option()`, and
options with option modes are configured via
:cpp:func:`bitwuzla_set_option_mode()`.

The configured value of Boolean and numeric options can be queried via
:cpp:func:`bitwuzla_get_option()`,
and the value of an option with modes can be queried via
:cpp:func:`bitwuzla_get_option_mode()`.

The option kind is defined via :cpp:enum:`BitwuzlaKind`.
A **comprehensive list** of all configurable options is available
:doc:`here <enums/bitwuzlaoption>`.

Example
-------

The source code for this example can be found at `examples/c/options.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/options.c>`_.

.. literalinclude:: ../../examples/c/options.c
     :language: c

OptionInfo
----------

Bitwuzla offers a compact way to retrieve all information about a configuration
option as a :cpp:struct:`BitwuzlaOptionInfo` object via
:cpp:func:`bitwuzla_get_option_info()`.
This object is created per option and can be queried for any available
information, e.g., long and short option names, description, (current, default,
minimum and maximum) values for numeric options, and (current, default and
available) modes for configuration options with modes.
