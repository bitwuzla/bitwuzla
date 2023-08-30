.. _python_options:

Options
========

A :class:`bitwuzla.Bitwuzla` instance is created from a configuration
options :class:`bitwuzla.Options` instance. This options instance must
be configured before creating the Bitwuzla instance: **after** the Bitwuzla
instance is created, configuration options are fixed and **cannot** be changed.

**Bitwuzla** supports three kinds of options: Boolean options, numeric options
and options with option modes.
The kind of an option can be queried via
:obj:`bitwuzla.Options.is_bool()`,
:obj:`bitwuzla.Options.is_numeric()`, and
:obj:`bitwuzla.Options.is_mode()`.

All options are configured via :obj:`bitwuzla.Options.set()`.
Additionally, it is also possible to configure options in batch via
:obj:`bitwuzla.Options.set_args()`,
where the given arguments are each a command line option configuration string,
e.g., :code:`set_args("-i", "--produce-models=true", "--produce-unsat-cores true")`.

The configured value of options can be queried via :obj:`bitwuzla.Options.get()`.

The short name of an option can be queried via :obj:`bitwuzla.Options.shrt()`,
its long name via :obj:`bitwuzla.Options.lng()`, its description via
:obj:`bitwuzla.Options.description()`,
and, if given option is an option with modes, its modes can be queried via
:obj:`bitwuzla.Options.modes()`.

The option kind is defined via :class:`bitwuzla.Option`.
A **comprehensive list** of all configurable options is available
:doc:`here <enums/option>`.

Example
-------

The source code for this example can be found at `examples/python/options.py <https://github.com/bitwuzla/bitwuzla/tree/main/examples/python/options.py>`_.

.. literalinclude:: ../../examples/python/options.py
     :language: python
