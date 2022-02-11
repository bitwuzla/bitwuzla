.. _c_options:

Options
=======

**Bitwuzla** supports two kinds of options: options that expect an unsigned
integer as option value and are configured via :c:func:`bitwuzla_set_option()`,
and options that are configured via a value string with
:c:func:`bitwuzla_set_option_str()`.
For example, the following will enable the propagation-based local search
solver engine, enable model generation and set the verbosity level to 2.

.. literalinclude:: ../../examples/c/options.c
     :language: c
     :lines: 17,25,27

The current configuration value of an option can be queried via
:c:func:`bitwuzla_get_option()` (for integer configuration values, supported
for all options) and :c:func:`bitwuzla_get_option_str()` (for string
configuration values, only supported for options that support string
configuration values).

.. literalinclude:: ../../examples/c/options.c
     :language: c
     :lines: 11-14

This will print:

.. code-block::

  Default engine: fun (enum value: 1)

Example
-------

The source code for this example can be found at `examples/c/options.c <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/options.c>`_.

.. literalinclude:: ../../examples/c/options.c
     :language: c

A Comprehensive List of All Configurable Options
------------------------------------------------

The kind of an option is defined via enum :c:enum:`BitwuzlaOption`.

.. note::

  Some options are labeled as "expert" options. Use with caution.

.. doxygenenum:: BitwuzlaOption

