API:
- enum `BitwuzlaOption`:
  +  `SAT_ENGINE` -> `SAT_SOLVER`

- enum `BitwuzlaBVBase` -> `uint8_t` in { 2, 10, 16 }
  + `bitwuzla_mk_bv_value(Bitwuzl*, const BitwuzlaSort*, const char*, BitwuzlaBVBase)` ->
    `bitwuzla_mk_bv_value(BitwuzlaSort, const char*, uint8_t)`

- struct `BitwuzlaOptionInfo`:
  + struct `numeric`:
    * `cur_val` -> `cur`
    * `def_val` -> `dflt`
    * `min_val` -> `min`
    * `max_val` -> `max`
  + struct `string`:
    * renamed to `mode`
    * `cur_val` -> `cur`
    * `def_val` -> `dflt`
    * `num_values` -> `num_modes`
    * `values` -> `modes`

- enum `BitwuzlaKind`:
  + `BITWUZLA_KIND_CONST` -> `BITWUZLA_KIND_CONSTANT`
  + `BITWUZLA_KIND_VAL`   -> `BITWUZLA_KIND_VALUE`
  + `BITWUZLA_KIND_VAR`   -> `BITWUZLA_KIND_VARIABLE`
  + `BITWUZLA_KIND_FP_EQ` -> `BITWUZLA_KIND_FP_EQUAL`

- `BitwuzlaTerm` is now a `uint64_t` instead of a struct
- `BitwuzlaSort` is now a `uint64_t` instead of a struct
- All functions that took `const BitwuzlaTerm*` and `const BitwuzlaSort*`
  now take `BitwuzlaTerm` and `BitwuzlaSort` as arguments.

- Functions to set and get options (option info) changed their signature and/or name.
  In particular, they now take a `BitwuzlaOptions*` instead of `Bitwuzla*` argument:
  + Create options instance with `bitwuzla_options_new()`
  + Delete options instance with `bitwuzla_options_delete(BitwuzlaOptions*)`
  + `bitwuzla_set_option(Bitwuzla*, BitwuzlaOption, uint32_t)` ->
    `bitwuzla_set_option(BitwuzlaOptions*, BitwuzlaOption, uint64_t)`
  + `bitwuzla_set_option_str(Bitwuzla*, BitwuzlaOption, const char*)` ->
    `bitwuzla_set_option_mode(BitwuzlaOptions, BitwuzlaOption, const char*)`
  + `bitwuzla_get_option_info(Bitwuzla*, BitwuzlaOption, BitwuzlaOptionInfo*)` ->
    `bitwuzla_get_option_info(BitwuzlaOptions*, BitwuzlaOption, BitwuzlaOptionInfo*)`

- Bitwuzla struct is now instantiated with BitwuzlaOptions instance:
  + Create bitwuzla instance with `bitwuzla_new(BitwuzlaOptions*)`
  + Delete options instance with `bitwuzla_delete(Bitwuzla*)`

- `bitwuzla_mk_*` functions do not take `Bitwuzla*` as an argument anymore

- `bitwuzla_push(Bitwuzla*, uint32_t)` -> `bitwuzla_push(Bitwuzla*, uint64_)`
- `bitwuzla_pop(Bitwuzla*, uint32_t)` -> `bitwuzla_pop(Bitwuzla*, uint64_)`

- `bitwuzla_get_unsat_assumptions` now returns a `BitwuzlaTerm*` instead of
  `const BitwuzlaTerm**`
- `bitwuzla_get_unsat_core` now returns a `BitwuzlaTerm*` instead of
  `const BitwuzlaTerm**`
- `bitwuzla_sort_get_fun_get_domain_sorts` now returns a `BitwuzlaTerm*` instead of
  `const BitwuzlaTerm**`

- Remove support for `bitwuzla_assume`, introduce `bitwuzla_check_sat_assuming`
- Remove support for `bitwuzla_fixate_assumptions` and `bitwuzla_reset_assumptions`

- `bitwuzla_get_fp_value` now additionally takes the numeric base in which the
   output value string is given as an argument:
   `bitwuzla_get_bv_value(Bitwuzla*, const BitwuzlaTerm*)` ->
   `bitwuzla_get_bv_value(Bitwuzla*, BitwuzlaTerm, uint8_t)`

- `bitwuzla_get_fp_value` now also takes the numeric base in which the output
  value string is given as an argument:
  `bitwuzla_get_fp_value(Bitwuzla*, const BitwuzlaTerm*, const char**, const char**, const char**)` ->
  `bitwuzla_get_fp_value(Bitwuzla*, BitwuzlaTerm, const char**, const char**, const char**, uint8_t)`

- `bitwuzla_get_rm_value` now returns a BitwuzlaRoundingMode instead of a string

- Remove support for `bitwuzla_get_array_value`
- Remove support for `bitwuzla_get_fun_value`
- Remove support for `bitwuzla_print_model`


## TODO
- changes in parsing functions
- changes for printing sorts, terms
- changes for printing the formula
- changes for (in)valid option combinations
