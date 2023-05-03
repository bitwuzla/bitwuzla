Options
--------

A :cpp:class:`bitwuzla::Bitwuzla` instance is created from a configuration
options :cpp:class:`bitwuzla::Options` instance.

.. note::

   This options instance must be configured before creating the Bitwuzla
   instance. **After** the Bitwuzla instance is created, configuration options
   are fixed and **cannot** be changed.

Every option can be configured via
:cpp:func:`void bitwuzla::Options::set(const std::string &lng, const std::string &value)`.
Additionally, Boolean and numeric options are configured via
:cpp:func:`void bitwuzla::Options::set(Option option, uint64_t value)`, and
options with modes are configured via
:cpp:func:`void bitwuzla::Options::set(Option option, const std::string& value)`.
The option kind is defined via :cpp:enum:`bitwuzla::Option`.
A **comprehensive list** of all configurable options is available
:doc:`here <cpp/enums/option>`.

More information on and an example for how to configure and query configuration
options is :doc:`here </cpp/options>`.

.. note::

  Some options are labeled as "expert" options. Use with caution.

----

- class :cpp:class:`bitwuzla::Options`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::Options
    :project: Bitwuzla_cpp
    :members:

:code:`}`
