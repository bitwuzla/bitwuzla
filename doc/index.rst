Welcome to Boolector's API documentation!
=========================================

Introduction
------------

  Boolector_ is an SMT solver for the quantifier-free theory of bit vectors
  with arrays. It supports BZLA_, `SMT-LIB v1`_, and `SMT-LIB v2`_
  as input format and can be either used as a stand-alone SMT solver, or as
  back end for other tools via its public API.
  This is the documentation of Boolector's public **C interface** and
  **Python interface**.
  For further information and the latest version of Boolector, please refer
  to https://boolector.github.io.

  .. _Boolector: https://boolector.github.io
  .. _BTOR: http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf
  .. _SMT-LIB v1: http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf
  .. _SMT-LIB v2: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf


API Documentations
------------------

.. toctree::
    :maxdepth: 2

    cboolector
    pyboolector
