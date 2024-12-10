Exception
---------

- class :cpp:class:`bitwuzla::Exception`
- class :cpp:class:`bitwuzla::option::Exception`
- class :cpp:class:`bitwuzla::parser::Exception`

----

The C++ API of Bitwuzla communicates errors via exceptions. The base class for
all exceptions is :cpp:class:`bitwuzla::Exception`.
Configuration errors that occur while setting up :cpp:class:`bitwuzla::Options`
throw a :cpp:class:`bitwuzla::option::Exception`, and errors encountered while
parsing throw a :cpp:class:`bitwuzla::parser::Exception`.

In general, exceptions indicate that the associated object may be in an unsafe
state and should no longer be used. An exception to this rule are option
exceptions, which are thrown before the state of the associated option object
is modified and thus allow recovering from configuration errors. That is,
if a :cpp:class:`bitwuzla::option::Exception` is throw, the associated
:cpp:class:`bitwuzla::Options` object can still be used.

----

:code:`namespace bitwuzla {`

.. doxygenclass:: bitwuzla::Exception
    :project: Bitwuzla_cpp
    :members:

:code:`namespace bitwuzla::option {`

.. doxygenclass:: bitwuzla::option::Exception
    :project: Bitwuzla_cpp
    :members:

:code:`}`

:code:`namespace bitwuzla::parser {`

.. doxygenclass:: bitwuzla::parser::Exception
    :project: Bitwuzla_cpp
    :members:

:code:`}`
:code:`}`
