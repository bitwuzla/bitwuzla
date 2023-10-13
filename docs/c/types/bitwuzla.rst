Bitwuzla
--------

A :cpp:struct:`Bitwuzla` instance is created from a configuration
options :cpp:struct:`BitwuzlaOptions` instance. This options instance must be
configured before creating the Bitwuzla instance: **after** the Bitwuzla
instance is created, configuration options are fixed and **cannot** be changed.
:cpp:struct:`BitwuzlaSorts <BitwuzlaSort>` and
:cpp:struct:`BitwuzlaTerms <BitwuzlaTerm>` are **independent** of a
:cpp:struct:`Bitwuzla` instance and can be shared across Bitwuzla
instances.

A Bitwuzla instance is created via :cpp:func:`bitwuzla_new()` and must be
released via :cpp:func:`bitwuzla_delete()`.

Bitwuzla supports **incremental solving** via
:cpp:func:`bitwuzla_push()` and :cpp:func:`bitwuzla_pop()`;
querying the solver for the current set of assertions via
:cpp:func:`bitwuzla_get_assertions()`,
model values via :cpp:func:`bitwuzla_get_value()`,
the unsat core via :cpp:func:`bitwuzla_get_unsat_core()`,
and unsat assumptions via :cpp:func:`bitwuzla_get_unsat_assumptions`;
and printing the currently asserted formula via
:cpp:func:`bitwuzla_print_formula()`.
The current statistics can be retrieved as a mapping from statistic names
to values via :cpp:func:`bitwuzla_get_statistics()`.

Bitwuzla further supports configuring a **termination callback** via
:cpp:func:`bitwuzla_set_termination_callback()`, which allows to terminate
Bitwuzla prematurely, during solving. This termination callback returns a
:code:`int32_t` to indicate if Bitwuzla should be terminated. Bitwuzla
periodically checks this callback and terminates at the earliest possible
opportunity if the callback function returns a value :code:`!= 0`.

----

- typedef struct :cpp:struct:`Bitwuzla`
- :cpp:func:`bitwuzla_new()`
- :cpp:func:`bitwuzla_delete()`
- :cpp:func:`bitwuzla_terminate()`
- :cpp:func:`bitwuzla_set_termination_callback()`
- :cpp:func:`bitwuzla_get_termination_callback_state()`
- :cpp:func:`bitwuzla_set_abort_callback()`
- :cpp:func:`bitwuzla_push()`
- :cpp:func:`bitwuzla_pop()`
- :cpp:func:`bitwuzla_assert()`
- :cpp:func:`bitwuzla_get_assertions()`
- :cpp:func:`bitwuzla_is_unsat_assumption()`
- :cpp:func:`bitwuzla_get_unsat_assumptions()`
- :cpp:func:`bitwuzla_get_unsat_core()`
- :cpp:func:`bitwuzla_simplify()`
- :cpp:func:`bitwuzla_check_sat()`
- :cpp:func:`bitwuzla_check_sat_assuming()`
- :cpp:func:`bitwuzla_get_value()`
- :cpp:func:`bitwuzla_print_formula()`
- :cpp:func:`bitwuzla_get_statistics()`

----

.. doxygentypedef:: Bitwuzla
    :project: Bitwuzla_c

----

.. doxygengroup:: c_bitwuzla
    :project: Bitwuzla_c
    :content-only:

