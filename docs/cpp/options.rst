.. _cpp_options:

Options
========

A :cpp:class:`bitwuzla::Bitwuzla` instance is created from a configuration
options :cpp:class:`bitwuzla::Options` instance. This options instance must
be configured before creating the Bitwuzla instance: **after** the Bitwuzla
instance is created, configuration options are fixed and **cannot** be changed.

**Bitwuzla** supports three kinds of options: Boolean options, numeric options
and options with option modes.
The kind of an option can be queried via
:cpp:func:`bool bitwuzla::Options::is_bool(Option option) const`,
:cpp:func:`bool bitwuzla::Options::is_numeric(Option option) const`, and
:cpp:func:`bool bitwuzla::Options::is_mode(Option option) const`.

Boolean and numeric options are configured via
:cpp:func:`void bitwuzla::Options::set(Option option, uint64_t value)`, and
options with option modes are configured via
:cpp:func:`void bitwuzla::Options::set(Option option, const std::string& value)`.
Any option can also be configured via
:cpp:func:`void bitwuzla::Options::set(const std::string &lng, const std::string &value)`,
where :code:`lng` is the long name of the option (e.g., :code:`"produce-models"`).

Additionally, it is also possible to configure options in batch via
:cpp:func:`void bitwuzla::Options::set(const std::vector<std::string> &args)`,
where :code:`args` is a vector of command line option configuration strings,
e.g., :code:`{"-i", "--produce-models=true", "--produce-unsat-cores true"}`.

The configured value of Boolean and numeric options can be queried via
:cpp:func:`uint64_t bitwuzla::Options::get(Option option) const`,
and the value of an option with modes can be queried via
:cpp:func:`const std::string& bitwuzla::Options::get_mode(Option option) const`.

The short name of an option can be queried via
:cpp:func:`const char* bitwuzla::Options::shrt(Option option) const`,
its long name via
:cpp:func:`const char* bitwuzla::Options::lng(Option option) const`,
its description via
:cpp:func:`const char* bitwuzla::Options::description(Option option) const`,
and, if given option is an option with modes, its modes can be queried via
:cpp:func:`std::vector<std::string> bitwuzla::Options::modes(Option option) const`.

The option kind is defined via :cpp:enum:`bitwuzla::Option`.
A **comprehensive list** of all configurable options is available
:doc:`here <enums/option>`.

Example
-------

The source code for this example can be found at `examples/c/options.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/c/options.cpp>`_.

.. literalinclude:: ../../examples/cpp/options.cpp
     :language: cpp

OptionInfo
----------

Bitwuzla offers a compact way to retrieve all information about a configuration
option as a :cpp:struct:`bitwuzla::OptionInfo` object via
:cpp:func:`bitwuzla::OptionInfo::OptionInfo()`.
This object is created per option and can be queried for the same information
as :cpp:class:`bitwuzla::Options`.
