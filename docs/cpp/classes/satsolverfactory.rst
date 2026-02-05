SatSolverFactory
----------------

The SAT solver factory of a Bitwuzla instance.

By default, Bitwuzla maintains an internal SAT solver factory to create SAT
solver instances and no user intervention is required.

However, optionally, Bitwuzla also supports configuring an external,
user-provided SAT solver factory via class
:cpp:class:`bitwuzla::SatSolverFactory`.
If configured, this factory generates new :cpp:class:`bitwuzla::SatSolver`
instances.

An external SAT solver factory is configured via constructor
:cpp:func:`bitwuzla::Bitwuzla bitwuzla::Bitwuzla::Bitwuzla(TermManager&, SatSolverFactory&, const Options&)`.

----

- class :cpp:class:`bitwuzla::SatSolverFactory`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::SatSolverFactory
    :project: Bitwuzla_cpp
    :members:

:code:`}`
