C Interface
===========

* :ref:`c/interface:types`
* :ref:`c/interface:enums`
* :ref:`c/interface:functions`

---------


Types
-----

Bitwuzla
^^^^^^^^
.. doxygentypedef:: Bitwuzla
    :project: Bitwuzla_c

BitwuzlaOptions
^^^^^^^^^^^^^^^
.. doxygentypedef:: BitwuzlaOptions
    :project: Bitwuzla_c

BitwuzlaSort
^^^^^^^^^^^^
.. doxygentypedef:: BitwuzlaSort
    :project: Bitwuzla_c

BitwuzlaTerm
^^^^^^^^^^^^
.. doxygentypedef:: BitwuzlaTerm
    :project: Bitwuzla_c

BitwuzlaParser
^^^^^^^^^^^^^^
.. doxygentypedef:: BitwuzlaParser
    :project: Bitwuzla_c


Enums
------

BitwuzlaKind
^^^^^^^^^^^^
See :ref:`c/kinds:kinds` for more details and examples on how to create terms
of a given kind.

BitwuzlaOption
^^^^^^^^^^^^^^
See :ref:`c/options:options` for more details and examples on how to set and
get options.

BitwuzlaOptionInfo
^^^^^^^^^^^^^^^^^^
.. doxygenstruct:: BitwuzlaOptionInfo
    :project: Bitwuzla_c
    :members:

BitwuzlaResult
^^^^^^^^^^^^^^^
.. doxygenenum:: BitwuzlaResult
    :project: Bitwuzla_c

BitwuzlaRoundingMode
^^^^^^^^^^^^^^^^^^^^^
.. doxygenenum:: BitwuzlaRoundingMode
    :project: Bitwuzla_c


Functions
---------

.. doxygenfile:: bitwuzla.h
    :project: Bitwuzla_c
    :sections: func

.. doxygenfile:: parser.h
    :project: Bitwuzla_c
    :sections: func
