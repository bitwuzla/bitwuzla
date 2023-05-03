Terminator
----------

The termination callback configuration of a Bitwuzla instance.

Bitwuzla supports configuring a termination callback via class
:cpp:class:`bitwuzla::Terminator`, which implements a callback function
:cpp:class:`bitwuzla::Terminator::terminate()` to allow terminating
Bitwuzla prematurely, during solving. This termination callback returns a
:code:`bool` to indicate if Bitwuzla should be terminated. Bitwuzla
periodically checks this callback and terminates at the earliest possible
opportunity if the callback function returns :code:`true`.

A terminator is connected to a Bitwuzla instance via
:cpp:func:`bitwuzla::Bitwuzla::configure_terminator()`. Note that only one terminator
can be connected to a Bitwuzla instance at a time.

----

- class :cpp:class:`bitwuzla::Terminator`
- :ref:`cpp/classes/terminator:example`

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::Terminator
    :project: Bitwuzla_cpp
    :members:

:code:`}`

----

Example
^^^^^^^

The source code for this example can be found at `examples/c/terminator.cpp <https://github.com/bitwuzla/bitwuzla/tree/main/examples/cpp/terminator.cpp>`_.

.. literalinclude:: ../../../examples/cpp/terminator.cpp
     :language: cpp
