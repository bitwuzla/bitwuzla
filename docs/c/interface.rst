C Interface
===========

This section provides a detailed description of the :doc:`C API <api>` of Bitwuzla.
For an introduction on how to use the C API, refer to the
:ref:`quickstart <c/api:quickstart>` guide. A comprehensive set of
:ref:`examples <c/api:examples>` covers basic and common use cases.

One of the key differences between the C and the C++ APIs is the way **how
memory is managed**. While users of the C++ API can rely on memory being
efficiently managed automatically, on the C level, management to maintain a low
overhead needs **more manual intervention**.

The C API offers **two modes** of memory management:

1. Let Bitwuzla handle memory management without manual intervention. All
   memory allocated by the C API via a term manager
   (:cpp:type:`BitwuzlaTermManager`) or solver (:cpp:type:`Bitwuzla`) instance
   will only be released when these instances are
   deleted via :cpp:func:`bitwuzla_delete()` and
   :cpp:func:`bitwuzla_term_manager_delete()`.
   For example:

.. code:: c

    BitwuzlaOptions *options = bitwuzla_options_new();
    BitwuzlaTermManager *tm  = bitwuzla_term_manager_new();
    Bitwuzla *bitwuzla       = bitwuzla_new(tm, options);
    BitwuzlaTerm a        = bitwuzla_mk_const(tm, bitwuzla_mk_bool_sort(tm), "a");
    BitwuzlaTerm btrue    = bitwuzla_mk_true(tm);
    BitwuzlaTerm args1[2] = {a, btrue};
    bitwuzla_assert(bitwuzla,
                    bitwuzla_mk_term(tm, BITWUZLA_KIND_EQUAL, 2, args1));
    BitwuzlaTerm b        = bitwuzla_mk_const(tm, bitwuzla_mk_bool_sort(tm), "b");
    BitwuzlaTerm args2[2] = {b, btrue};
    bitwuzla_assert(bitwuzla,
                    bitwuzla_mk_term(tm, BITWUZLA_KIND_DISTINCT, 2, args2));
    bitwuzla_check_sat(bitwuzla);
    bitwuzla_delete(bitwuzla);
    bitwuzla_term_manager_delete(tm);
    bitwuzla_options_delete(options);

2. Introduce a more fine-grained, user-level memory management for objects
   created via a term manager or solver via the corresponding
   ``bitwuzla_*_copy()`` and ``bitwuzla_*_release()`` functions. The copy
   functions increment the reference counter of an object, the release
   functions decrement the reference counter and free its allocated memory when
   the counter reaches 0. For example:

.. code:: c

    BitwuzlaOptions *options = bitwuzla_options_new();
    BitwuzlaTermManager *tm  = bitwuzla_term_manager_new();
    Bitwuzla *bitwuzla       = bitwuzla_new(tm, options);
    BitwuzlaTerm a        = bitwuzla_mk_const(tm, bitwuzla_mk_bool_sort(tm), "a");
    BitwuzlaTerm btrue    = bitwuzla_mk_true(tm);
    BitwuzlaTerm args1[2] = {a, btrue};
    bitwuzla_assert(bitwuzla,
                    bitwuzla_mk_term(tm, BITWUZLA_KIND_EQUAL, 2, args1));
    // we can release 'a' here, not needed anymore
    bitwuzla_term_release(a);
    BitwuzlaTerm b        = bitwuzla_mk_const(tm, bitwuzla_mk_bool_sort(tm), "b");
    BitwuzlaTerm args2[2] = {b, btrue};
    bitwuzla_assert(bitwuzla,
                    bitwuzla_mk_term(tm, BITWUZLA_KIND_DISTINCT, 2, args2));
    bitwuzla_check_sat(bitwuzla);
    bitwuzla_delete(bitwuzla);
    bitwuzla_term_manager_delete(tm);
    bitwuzla_options_delete(options);

.. container:: hide-toctree

  .. toctree::
     :hidden:

     types/bitwuzla
     enums/bitwuzlakind
     enums/bitwuzlaoption
     structs/bitwuzlaoptioninfo.rst
     types/bitwuzlaoptions
     types/bitwuzlaparser
     enums/bitwuzlaresult
     enums/bitwuzlaroundingmode
     types/bitwuzlasort
     types/bitwuzlaterm
     types/bitwuzlatermmanager
     library_info


Types
-----

- typedef struct :doc:`types/bitwuzlatermmanager`
- typedef struct :doc:`types/bitwuzlaoptions`
- typedef struct :doc:`types/bitwuzla`
- typedef struct :doc:`types/bitwuzlasort`
- typedef struct :doc:`types/bitwuzlaterm`
- typedef struct :doc:`types/bitwuzlaparser`

Structs
-------

- struct :doc:`structs/bitwuzlaoptioninfo`

Enums
------

- enum :doc:`enums/bitwuzlakind`
- enum :doc:`enums/bitwuzlaoption`
- enum :doc:`enums/bitwuzlaresult`
- enum :doc:`enums/bitwuzlaroundingmode`


Functions
---------

- :doc:`library_info`
