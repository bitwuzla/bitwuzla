SatSolver
---------

The SAT solver instance of a Bitwuzla instance.

By default, Bitwuzla creates :cpp:class:`bitwuzla::SatSolver` instances
internally and no user intervention is required.

However, optionally, also Bitwuzla supports configuring an external,
user-provided SAT solver factory via class
:cpp:class:`bitwuzla::SatSolverFactory`, which generates new
:cpp:class:`bitwuzla::SatSolver` instances.

----

- class :cpp:class:`bitwuzla::SatSolver`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::SatSolver
    :project: Bitwuzla_cpp
    :members:

:code:`}`

