Bitwuzla
--------

A :cpp:class:`bitwuzla::Bitwuzla` instance is created from a configuration
options :cpp:class:`bitwuzla::Options` instance. This options instance must be
configured before creating the Bitwuzla instance: **after** the Bitwuzla
instance is created, configuration options are fixed and **cannot** be changed.
:cpp:class:`bitwuzla::Sorts <bitwuzla::Sort>` and
:cpp:class:`bitwuzla::Terms <bitwuzla::Term>` are **independent** of a
:cpp:class:`bitwuzla::Bitwuzla` instance and can be shared across Bitwuzla
instances.

Bitwuzla supports **incremental solving** via
:cpp:func:`bitwuzla::Bitwuzla::push()` and
:cpp:func:`bitwuzla::Bitwuzla::pop()`;
querying the solver for the current set of assertions via
:cpp:func:`bitwuzla::Bitwuzla::get_assertions()`,
model values via :cpp:func:`bitwuzla::Bitwuzla::get_value()`,
the unsat core via :cpp:func:`bitwuzla::Bitwuzla::get_unsat_core()`,
and unsat assumptions via :cpp:func:`bitwuzla::Bitwuzla::get_unsat_assumptions`;
and printing the currently asserted formula via
:cpp:func:`bitwuzla::Bitwuzla::print_formula()`.
The current statistics can be retrieved as a mapping from statistic names
to values via :cpp:func:`bitwuzla::Bitwuzla::statistics()`.

Bitwuzla further supports configuring a **termination callback** via
:cpp:class:`bitwuzla::Terminator`, which implements a callback function
:cpp:class:`bitwuzla::Terminator::terminate()` to allow terminating
Bitwuzla prematurely, during solving. This termination callback returns a
:code:`bool` to indicate if Bitwuzla should be terminated. Bitwuzla
periodically checks this callback and terminates at the earliest possible
opportunity if the callback function returns :code:`true`.

----

- class :cpp:class:`bitwuzla::Bitwuzla`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::Bitwuzla
    :project: Bitwuzla_cpp
    :members:

:code:`}`
