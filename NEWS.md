# News

This file collects a summary of important and/or user-visible changes.

## News for version 0.6.0

- Added new **abstraction module** for abstracting bit-vector arithmetic
  operators, see [Aina Niemetz, Mathias Preiner and Yoni Zohar. Scalable
  Bit-Blasting with Abstractions. CAV 2024, Springer, 2024.](
  https://doi.org/10.1007/978-3-031-65627-9_9).
  Enable with option `--abstraction`, the minimum bit-width of relevant terms
  to abstract can be configured via option `--abstraction-bv-size`.

- **Quantification over array variables** now supported.

- Improved arithmetic **normalization**.

- Added new **command-line option** `--print-model`. This enables auto-printing
  of models after a satisfiable query. Must be enabled to print models for
  BTOR2 input (automatically enables `-m`). Command line option `-m`,
  `--produce-models` alone now does not print models for BTOR2 input anymore.

- Parser now allows to configure auto-printing of models (corresponding to
  command-line option `--print-model` above) via:
  - C++ API: `Parser::configure_auto_print_model(bool)`
  - C API: `bitwuzla_parser_configure_auto_print_model(BitwuzlaParser*,bool)`
  - Python API: `Parser.configure_auto_print_model(bool)`

- Bumped Kissat to version 4.0.1.

- Fixed version string generation for dev versions. Previously, git information
  that is included in the version string was not regenerated at compile time,
  only at configure time.


## News for version 0.5.0

- Fixed incorrect result with rewrite level 0 (issue #110) (missing guard,
  normalization preprocessing pass expects terms to be fully rewritten).

- Refactored **node data** storage and unique table handling, **improves**
  performance and memory footprint.

- Added support for **BTOR2 model printing**.

- Added support for querying the **parser** for declared sorts and terms.
  + C++ API:
    * New Function `Parser::get_declared_sorts()` to retrieve user-declared
      sorts (SMT-LIB: declared via `declare-sort`, BTOR2: always empty).
    * New Function `Parser::get_declared_funs()` to retrieve user-declared
      function symbols (SMT-LIB: declared via `declare-const` and `declare-fun`,
      BTOR2: inputs with a symbol).
  + C API:
    * New Function `bitwuzla_parser_get_declared_sorts(BitwuzlaParser*, size_t*)`.
    * New Function `bitwuzla_parser_get_declared_funs(BitwuzlaParser*, size_t*)`.
  + Python API:
    * New Function `Parser.get_declared_sorts()`.
    * New Function `Parser.get_declared_funs()`.

- Refactored statistics printing to not print NaN values.

- Improved logging and statistics for local search engine.

- Several improvements to build system configuration.

- Several fixes for Windows cross compilation.

## News for version 0.4.0

- Added Linux aarch64 cross-compilation support (configure flag: `--arm64`).

- Introduce **TermManager interface** for creating Term and Sort
  (**major API change**).
  + Solver and parser instances now require a term manager for initialization.
    Terms and sorts can be shared across solver/parser instances if they were
    initialized with the same term manager. The term manager is responsible for
    managing Term and Sort objects.
  + C++ API:
    * New class `TermManager` for creating Term and Sort objects.
    * Term and Sort creation function `mk_*` moved to `TermManager` class.
    * Substitution functions `substitute_term` and `substitute_terms` moved
      to `TermManager`.
    * Constructor `Bitwuzla(const Options &options)` changed to
      `Bitwuzla(TermManager&, const Options &options)`.
    * New function `Bitwuzla::term_mgr()` to retrieve configured term manager
      instance.
  + C API:
    * New functions `bitwuzla_term_manager_new()`,
      `bitwuzla_term_manager_delete` for creating and deleting term manager
      instances.
    * Function `bitwuzla_new(const BitwuzlaOptions*)` changed to
      `bitwuzla_new(BitwuzlaTermManager*, const BitwuzlaOptions*)`.
    * New function `bitwuzla_get_term_mgr(Bitwuzla*)` to retrieve configured term
      manager instance from Bitwuzla instance.
    * New reference counting interface for fine-grained resource management:
      - New function `bitwuzla_term_manager_release(BitwuzlaTermManager*)` to release all created
        terms and sorts of a term manager instance.
      - New functions `bitwuzla_term_copy(BitwuzlaTerm)` and
        `bitwuzla_term_release(BitwuzlaTerm)` for
        incrementing/decrementing BitwuzlaTerm reference counts.
      - New functions `bitwuzla_sort_copy(BitwuzlaSort)` and
        `bitwuzla_sort_release(BitwuzlaSort)` for
        incrementing/decrementing BitwuzlaSort reference counts.
  + Python API:
    * New class `TermManager` for creating Term and Sort objects.
    * Term and Sort creation function `mk_*` moved to `TermManager` class.
    * Substitution functions `substitute_term` and `substitute_terms` moved
      to `TermManager`.
    * Constructor `Bitwuzla(Options)` changed to
      `Bitwuzla(TermManager, Options)`.
    * New function `Bitwuzla::term_mgr()` to retrieve configured term manager
      instance.


- Refactor **parser interface** to allow parsing from string inputs.
  + A parser instance is not tied to an input file anymore.
  + Added support for parsing from string inputs.
  + Added support for parsing terms and sorts from string inputs.
  + Interface for parsing functions now returns `bool` instead of string.
  + C++ API:
    * Constructor `Parser(Options&, const std::string&, const std::string&, std::ostream*)`
      changed to `Parser(TermManager&, Options&, const std::string&, std::ostream*)`
    * Function `std::string Parser::parse(bool)` changed to
      `void Parser::parse(const std::string, bool, bool)`
      and now throws an exception on error. It now also supports parsing from
      string input.
    * New Function `void Parser::parse(const std::string&, std::istream&, bool)`
      allows parsing from an already open input stream and now throws an
      exception on error. This function is not limited to input files but also
      supports parsing from `std::cin` and strings.
    * New function `bitwuzla::Term parse_term(const std::string&)` to
      parse a term from string.
    * New function `bitwuzla::Sort parse_sort(const std::string&)` to
      parse a sort from string.
    * New `bitwuzla::parser::Exception` (derived from `bitwuzla::Exception`)
      which is thrown on parse error.
  + C API:
    * Function `BitwulzaParser* bitwuzla_parser_new(BitwuzlaOptions*, const char*, FILE*, const char*, uint8_t, const char*)`
      changed to `BitwulzaParser* bitwuzla_parser_new(BitwuzlaTermManager*, BitwuzlaOptions*, const char*, uint8_t, const char*)`.
    * Function `const char* bitwuzla_parser_parse(BitwulzaParser*, bool)`
      changed to `void bitwuzla_parser_parse(BitwulzaParser*, const char*, bool, bool, const char*)`.
    * New function `const char* bitwuzla_parser_get_error_msg(BitwuzlaParser*)`
      to query error message.
    * New function `BitwuzlaTerm bitwuzla_parser_parse_term(BitwuzlaParser*, const char*, const char*)`
      to parse a term from string.
    * New function `BitwuzlaSort bitwuzla_parser_parse_sort(BitwuzlaParser*, const char*, const char*)`
      to parse a sort from string.
  + Python API:
    * Class `Parser` is now constructed from options, a language and a base
      for the string representation of bit-vector values (does not require
      an input file name anymore).
    * Function `Parser.parse(self, parse_only: bool) -> str` changed to
      `Parser.parse(self, infile_name, parse_only: bool, parse_file: bool) -> bool`.
    * New function `parse_term(self, iinput) -> Term` to parse term from string.
    * New function `parse_sort(self, iinput) -> Sort` to parse sort form string.

## News for version 0.3.2

- Fix special case handling for equality over constant arrays.

## News for version 0.3.1

- Added option `-M`/`--memory-limit` to set memory limit.

- Printer: Fix printing of empty formulas.

- SMT2 Parser: Fix error handling for indexed bit-vector values.

- Allow special case for equality over constant arrays. This is part of
  ongoing work towards generally allowing equality over constant arrays.

## News for version 0.3.0

- Added support for bit-vector overflow operator `bvnego`.

- Added `--lang` option for specifying input language.

- Added Windows cross-compilation support (configure flag: `--win64`).

- Python API changes:
    * Simplified Function `mk_bv_value(sort: Sort, value, uint8_t base = 2)`,
      changed to `mk_bv_value(sort: Sort, value, *args)` to allow, e.g.,
      `mk_bv_value(s, 2)` to create a bit-vector value representation `2`
      of sort `s` instead of `mk_bv_value(s, 2, 10)`.
    * Added support for term substitution via functions `substitute_term()` and
      `substitute_terms()`.

- C API changes:
    * Functions `bitwuzla_substitute_term()` and `bitwuzla_substitute_terms()`
      do not require the (previously already unused) `Bitwuzla*` argument
      anymore.
      - `bitwuzla_substitute_term(Bitwuzla*, BitwuzlaTerm, size_t, BitwuzlaTerm[], BitwuzlaTerm[])`
        changed to
        `bitwuzla_substitute_term(BitwuzlaTerm, size_t, BitwuzlaTerm[], BitwuzlaTerm[])`
      - `bitwuzla_substitute_terms(Bitwuzla*, BitwuzlaTerm[], size_t, BitwuzlaTerm[], BitwuzlaTerm[])`
        changed to
        `bitwuzla_substitute_term(BitwuzlaTerm[], size_t, BitwuzlaTerm[], BitwuzlaTerm[])`

- Internally, options now have a notion of "user configured". If an option was
  configured by the user, it will not be reconfigured internally. Previously,
  we did not reconfigure any options, but now we set defaults in case the BV
  solver is configured in "preprop" mode.

## News for version 0.2.0

- Python API changes:
    * New function `Bitwuzla.print_formula()` returns the current input formula
      as a string in the given format (currently, as in the C++/C APIs, only
      SMT-LIB2 is supported). This function can optionally be configured with
      a bv output number format.
    * Enum values for Kind, Result and RoundingMode can now be converted to
      their string representation via str().
    * Added support for input file parsing.
    * New function `Options.is_valid()` allows to query if a given options
      name is valid.
    * `Term.value()` now allows to retrieve FP values as a list of sign,
      exponent and significand bit-vector strings.
    * New function `Bitwuzla::statistics()` allows to retrieve the current
      statistics as a dictionary that maps statistic name to value (strings).

- Bitwuzla now supports configuring the output number format for bit-vector
  values. This is configured via the CLI option `--bv-output-format`, or
  via the output stream modifier `bitwuzla::set_bv_format` when printing
  bit-vector values via the API.
  * C API changes:
    - `bitwuzla_term_value_get_str(BitwuzlaTerm, uint8_t)` changed to  
      `bitwuzla_term_value_get_str(BitwuzlaTerm)`:  
      The parameter to configure the bv output number format when getting the
      string representation of a term is now dropped to simplify the default
      case. New API function
      `bitwuzla_term_value_get_str_fmt(BitwuzlaTerm, uint8_t)`
      now offers the previous behavior of this function.
    - New API function `bitwuzla_term_to_string_fmt(BitwuzlaTerm, uint8_t)`
      allows to configure the bv output number format when getting the
      string representation of a term.
    - New API function `bitwuzla_term_print_fmt(BitwuzlaTerm, FILE*, uint8_t)`  
      allows to configure the bv output number format when printing terms.
      Function `bitwuzla_term_print(BitwuzlaTerm)` remains unchanged and, as
      previously, defaults to binary bit-vector output format.
    - `bitwuzla_term_print_formula(Bitwuzla*, const char*, FILE*)` changed to  
      `bitwuzla_term_print_formula(Bitwuzla*, const char*, FILE*, uint8_t)`:  
      The bv output number format when printing the currently asserted input
      formula can now be configured via (new, required)
      parameter `uint8_t base`.
    - `bitwuzla_parser_new(BitwuzlaOptions*, const char*, FILE*, const char*)`
       changed to  
      `bitwuzla_parser_new(BitwuzlaOptions*, const char*, FILE*, const char*,
          uint8_t, const char*)`  
      `BitwuzlaParser` is now configured with a bv output number format
      (when printing model values) via (new, required) parameter `uint8_t base`,
      and the name of the output file (`<stdout>` to use `stdout`) via (new,
      required) parameter `const char* outfile_name`.
    - Renamed `BitwuzlaOptionInfo.desc` to `description` for consistency
      between C and C++ API.
  * C++ API changes:
    - New stream modifier `set_bv_format(uint8_t)` allows to configure the
      output number format of bit-vector values of any output stream.
    - `Term::str()` now takes an optional parameter `uint8_t base` (default:
       binary) to configure the bv output number format in the string
       representation of the term.
    - `bitwuzla::Parser` can now be configured with an output stream.
  * Python API changes:
    - New function `Term.str()`, which takes an optional parameter `base`
      (default: binary) to configure the bv output number format in the string
      representation of the term. Function `Term.__str__()` uses default binary
      bv output number format.

- The SMT2 parser is now less restrictive with respect to setting *unsupported
  options* and using *unsupported annotation attributes*. This is now ignored
  (with a warning at verbosity level > 0) rather than rejected with an error.

- Added command line option -t/--time-limit for specifying a time limit for
  the overall runtime of the binary.

- Added library option -T/--time-limit-per for specifying a time limit per
  satisfiability check.

- Command line option --verbose renamed to --verbosity for consistency with
  option kind.

## News for version 0.1.1.

Various fixes.

## News for version 0.1.0 since commit 1230d80

Bitwuzla release 0.1.0 is a complete from-scratch rewrite in C++.

A comprehensive **system description** was presented at CAV 2023:  
[Aina Niemetz and Mathias Preiner. Bitwuzla. CAV 2023, Springer, 2023.](
 https://doi.org/10.1007/978-3-031-37703-7_1)

Bitwuzla now provides a C++ API as its main API, with a Python and C API
based on top of it. Compared to commit
[1230d80](https://github.com/bitwuzla/bitwuzla/commit/1230d80),
the C API has been slightly simplified and refactored. All three APIs can be
considered largely stable, and will be locked in for release 1.0.

The most notable user-visible changes are listed below.

### Build System

- Bitwuzla now uses [meson](https://mesonbuild.com/) as build system.

### Input Languages

- Bitwuzla supports [SMT-LIB v2](https://smt-lib.org) and
  [BTOR2](https://github.com/Boolector/btor2tools) as input languages.
  Support for BTOR has been dropped.

### Term/Sort Handling and Multiple Solver Instances

- Terms and sorts are now independent from a solver instance and can be shared
  across instances.

### Configuration Options

- Incremental solving is now always enabled and thus option `INCREMENTAL`
  is removed.

- SMT-LIB option `:produce-unsat-assumptions` was previously always enabled,
  but must now be explicitly enabled via option `PRODUCE_UNSAT_ASSUMPTIONS`.

- Option `SAT_ENGINE` has been renamed to `SAT_SOLVER`.

- Option `RW_LEVEL` has been renamed to `REWRITE_LEVEL`.

- Bitwuzla solver instances are created from an options instance, and this
  options instance must be configured prior to creating the solver instance.
  After creating the solver instance, configuration options are frozen.

### Preprocessing

- Preprocessing API calls do not return a result anymore (`bitwuzla_simplify`
  in the C API, `Bitwuzla::simplify` in the  C++ API, `Bitwuzla.simplify`
  in the Python API).

- Preprocessin is now *fully incremental*. All preprocessing passes are applied
  to the current set of assertions, from all assertion levels (including
  assumptions), and simplifications derived from lower levels are applied to
  all assertions of higher levels.

### C API

- A `Bitwuzla` instance is now created from a `BitwuzlaOptions` instance, which
  must be configured prior to creating the solver instance. `Bitwuzla` and
  `BitwuzlaOptions` instances are created and deleted via:
  + `bitwuzla_options_new()`
  + `bitwuzla_options_delete(BitwuzlaOptions*)`
  + `bitwuzla_new(BitwuzlaOptions*)`
  + `bitwuzla_delete(Bitwuzla*)` (as before)

- `BitwuzlaTerm` is now a `uint64_t` instead of an anonymous struct.

- `BitwuzlaSort` is now a `uint64_t` instead of an anonymous struct.

- All functions with `const BitwuzlaTerm*` and `const BitwuzlaSort*` as
  arguments, now take `BitwuzlaTerm` and `BitwuzlaSort` as arguments.

- struct `BitwuzlaOptionInfo`:
  + struct `string` has been renamed to `mode`
  + The following fields in struct `numeric` have been renamed:
    * `cur_val` to `cur`
    * `def_val` to `dflt`
    * `min_val` to `min`
    * `max_val` to `max`
  + The following fields in struct `string` (now `mode`) have been renamed:
    * `cur_val` to `cur`
    * `def_val` to `dflt`
    * `num_values` to `num_modes`
    * `values` to `modes`

- Functions to set and get options (and option info data) changed their
  signature and/or have been renamed. In particular, they now take a
  `BitwuzlaOptions*` instead of `Bitwuzla*` as argument:
  + Create options instance with `bitwuzla_options_new()`
  + Delete options instance with `bitwuzla_options_delete(BitwuzlaOptions*)`
  + `uint32_t bitwuzla_get_option(Bitwuzla*, BitwuzlaOption)` changed to  
    `uint64_t bitwuzla_get_oiption(BitwuzlaOptions, BitwuzlaOption)`
  + `const char* bitwuzla_get_option_str(Bitwuzla*, BitwuzlaOption)` changed to  
    `const char* bitwuzla_get_oiption(BitwuzlaOptions, BitwuzlaOption)`
  + `bitwuzla_set_option(Bitwuzla*, BitwuzlaOption, uint32_t)` changed to  
    `bitwuzla_set_option(BitwuzlaOptions*, BitwuzlaOption, uint64_t)`
  + `bitwuzla_set_option_str(Bitwuzla*, BitwuzlaOption, const char*)` changed to  
    `bitwuzla_set_option_mode(BitwuzlaOptions, BitwuzlaOption, const char*)`
  + `bitwuzla_get_option_info(Bitwuzla*, BitwuzlaOption, BitwuzlaOptionInfo*)`
     changed to  
    `bitwuzla_get_option_info(BitwuzlaOptions*, BitwuzlaOption, BitwuzlaOptionInfo*)`

- The following kinds (enum `BitwuzlaKind`) have been renamed:
  + `BITWUZLA_KIND_CONST` to `BITWUZLA_KIND_CONSTANT`
  + `BITWUZLA_KIND_VAL`   to `BITWUZLA_KIND_VALUE`
  + `BITWUZLA_KIND_VAR`   to `BITWUZLA_KIND_VARIABLE`
  + `BITWUZLA_KIND_FP_EQ` to `BITWUZLA_KIND_FP_EQUAL`

- enum `BitwuzlaBVBase` has been removed and replaced with `uint8_t` in
  { 2, 10, 16 }. The signatures of the following functions has changed:
  + `bitwuzla_mk_bv_value(Bitwuzla*, const BitwuzlaSort*, const char*, BitwuzlaBVBase)`
     has changed to
    `bitwuzla_mk_bv_value(BitwuzlaSort, const char*, uint8_t)`

- The following API functions have been renamed:
  + `bitwuzla_mk_fp_value_from_real` to `bitwuzla_mk_fp_from_real`
  + `bitwuzla_mk_fp_value_from_rational` to `bitwuzla_mk_fp_from_rational`
  + `bitwuzla_dump_formula` to `bitwuzla_print_formula`
  + `bitwuzla_sort_dump` to `bitwuzla_print_sort`
  + `bitwuzla_term_dump` to `bitwulza_print_term`

- `bitwuzla_print_formula` currently only supports printing the current input
  formula in SMT-LIB format. Support for printing the circuit representation of
  the (bit-vector abstraction) of the current input formula in AIGER format
  as well as printing its CNF representation are planned.

- `bitwuzla_term_print` and `bitwuzla_sort_print` allow printing terms and sorts
   in SMT-LIB format only (previously, via `bitwuzla_term_dump` and
   `bitwuzla_sort_dump`, it was also possible to print them in the now
   unsupported BTOR format).

- The following API functions changed their signature:
  + All `bitwuzla_mk_*` functions do not require `Bitwuzla*` as argument anymore.
  + `bitwuzla_push(Bitwuzla*, uint32_t)` changed to
    `bitwuzla_push(Bitwuzla*, uint64_t)`
  + `bitwuzla_pop(Bitwuzla*, uint32_t)` changed to
    `bitwuzla_pop(Bitwuzla*, uint64_t)`
  + `bitwuzla_get_unsat_assumptions` now returns a `BitwuzlaTerm*` instead of
    `const BitwuzlaTerm**`
  + `bitwuzla_get_unsat_core` now returns a `BitwuzlaTerm*` instead of
    `const BitwuzlaTerm**`
  + `bitwuzla_sort_get_fun_get_domain_sorts` now returns a `BitwuzlaTerm*`
    instead of `const BitwuzlaTerm**`
  + `BitwuzlaResult simplify(Bitwuzla*)` changed to `void simplify(Bitwuzla*)`

- Removed support for `bitwuzla_assume`, solving under assumptions is now
  available via new API function
  `bitwuzla_check_sat_assuming(Bitwuzla*, uint32_t, BitwuzlaTerm[])`

- Removed support for obsolete functions
  + `bitwuzla_fixate_assumptions`
  + `bitwuzla_reset_assumptions`

- Removed support for `bitwuzla_term_set_symbol`

- Removed support for `bitwuzla_get_array_value`, use `bitwuzla_get_value` in
  combination with `bitwuzla_term_value_get_*` instead

- Removed support for `bitwuzla_get_bv_value`, use `bitwuzla_get_value` in
  combination with `bitwuzla_term_value_get_str` instead

- Removed support for `bitwuzla_get_fp_value`, use `bitwuzla_get_value` (in
  combination with `bitwuzla_term_value_get_str`) or
  `bitwuzla_term_value_get_fp_ieee` instead

- Removed support for `bitwuzla_get_fun_value`, use `bitwuzla_get_value` in
  combination with `bitwuzla_term_value_get_*` instead

- Renamed `bitwuzla_get_rm_value` to `bitwuzla_term_value_get_rm`, now returns
  a `BitwuzlaRoundingMode` instead of `const char*`. For a string
  representation, use `bitwuzla_get_value` in combination with
  `bitwuzla_term_value_get_str`.

- Removed support for `bitwuzla_print_model`, see `examples/c/quickstart.c` for
  an example of how to print the model.

- Removed support for `bitwuzla_reset`, discard current Bitwuzla instance and
  create new instance (with a new options instance) instead. Note: terms and
  sorts are not associated with a solver instance and will not be released when
  the current instance is released. See `examples/c/reset.c` for an example of
  how to reset a solver instance.

- SMT-LIB command `reset-assertions` is similarly simulated via discarding the
  current Bitwuzla instance and creating new instance with the same options
  instance instead. Note: terms and sorts are not associated with a solver
  instance and will not be released when the current instance is released.
  See `examples/c/reset_assertions.c` for an example of how to realize
  SMT-LIB command `reset-assertions`.

- The following parse functions are replaced by the new parser API (see below):
  + `bitwuzla_parse`
  + `bitwuzla_parse_format`

- New API functions:
  + `bitwuzla_option_is_numeric(BitwuzlaOptions*, BitwuzlaOption)`
  + `bitwuzla_option_is_mode(BitwuzlaOptions*, BitwuzlaOption)`
  + `bitwuzla_check_sat_assuming(Bitwuzla*, uint32_t, BitwuzlaTerm[])`
  + `bitwuzla_term_value_get_bool(BitwuzlaTerm)`
  + `bitwuzla_term_value_get_str(BitwuzlaTerm, uint8_t)`
  + `bitwuzla_term_value_get_rm(BitwuzlaTerm)`
  + `bitwuzla_term_to_string(BitwuzlaTerm term)`
  + `bitwuzla_sort_to_string(BitwuzlaSort sort)`
  + `bitwuzla_mk_uninterpreted_sort()`
  + `bitwuzla_sort_is_uninterpreted()`
  + `bitwuzla_term_is_uninterpreted()`
  + `bitwuzla_sort_get_uninterpreted_symbol(BitwuzlaSort)`
  + `bitwuzla_get_statistics()`

### Python API

- Module renamed to `bitwuzla` from `pybitwuzla`
- Functions and classes now reflect the functionality of the new C++ API

### Parser API

Bitwuzla now provides a clean C and C++ API for parsing input files. This API
will be extended with support for parsing terms and sorts from strings in the
future. Python bindings for the parser API will be made available in the future.

The C parser API is available at `include/bitwuzla/c/parser.h` and the C++
parser API is available at `include/bitwuzla/cpp/parser.h`.
