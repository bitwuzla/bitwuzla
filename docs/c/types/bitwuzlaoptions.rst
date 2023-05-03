BitwuzlaOptions
---------------

A :cpp:struct:`Bitwuzla` instance is created from a configuration
options :cpp:struct:`BitwuzlaOptions` instance via
:cpp:func:`bitwuzla_options_new()`, and must be released via
:cpp:func:`bitwuzla_options_delete()`.

.. note::

   This options instance must be configured before creating the Bitwuzla
   instance. **After** the Bitwuzla instance is created, configuration options
   are fixed and **cannot** be changed.

Boolean and numeric options are configured via
:cpp:func:`bitwuzla_set_option()`, and
options with option modes are configured via
:cpp:func:`bitwuzla_set_option_mode()`.
The option kind is defined via :cpp:enum:`BitwuzlaOption`.
A **comprehensive list** of all configurable options is available
:doc:`here <c/enums/bitwuzlaoption>`.

More information on and an example for how to configure and query configuration
options is :doc:`here </c/options>`.

.. note::

  Some options are labeled as "expert" options. Use with caution.

----

- typedef struct :cpp:struct:`BitwuzlaOptions`
- :cpp:func:`bitwuzla_options_new()`
- :cpp:func:`bitwuzla_options_delete()`
- :cpp:func:`bitwuzla_option_is_numeric()`
- :cpp:func:`bitwuzla_option_is_mode()`
- :cpp:func:`bitwuzla_set_option()`
- :cpp:func:`bitwuzla_set_option_mode()`
- :cpp:func:`bitwuzla_get_option()`
- :cpp:func:`bitwuzla_get_option_mode()`
- :cpp:func:`bitwuzla_get_option_info()`

----

.. doxygentypedef:: BitwuzlaOptions
    :project: Bitwuzla_c

----

.. doxygengroup:: c_bitwuzlaoptions
    :project: Bitwuzla_c
    :content-only:

