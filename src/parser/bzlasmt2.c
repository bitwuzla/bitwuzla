/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlasmt2.h"

#include <ctype.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>

#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlamsg.h"
#include "bzlaopt.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

static const char *
remove_prefix(const char *logic, const char *prefix)
{
  size_t len_logic  = strlen(logic);
  size_t len_prefix = strlen(prefix);
  if (len_prefix <= len_logic && strncmp(logic, prefix, len_prefix) == 0)
  {
    return logic + len_prefix;
  }
  return logic;
}

static bool
is_supported_logic(const char *logic)
{
  const char *p = logic;
  if (!strcmp(p, "ALL"))
  {
    return true;
  }
  p = remove_prefix(p, "QF_");
  p = remove_prefix(p, "A");
  p = remove_prefix(p, "UF");
  p = remove_prefix(p, "BV");
  p = remove_prefix(p, "FPLRA");
  p = remove_prefix(p, "FP");
  return strlen(p) == 0;
}

/*------------------------------------------------------------------------*/

BZLA_DECLARE_STACK(BitwuzlaTermConstPtr, const BitwuzlaTerm *);
BZLA_DECLARE_STACK(BitwuzlaSortConstPtr, const BitwuzlaSort *);

/*------------------------------------------------------------------------*/

BitwuzlaOption bitwuzla_get_option_from_string(Bitwuzla *bitwuzla,
                                               const char *str);

void bitwuzla_term_print_value_smt2(const BitwuzlaTerm *, char *, FILE *);
void bitwuzla_term_var_mark_bool(const BitwuzlaTerm *);

/*------------------------------------------------------------------------*/

typedef enum BzlaSMT2TagClass
{
  BZLA_CLASS_BITS_SMT2 = 6,
  BZLA_CLASS_SIZE_SMT2 = (1 << BZLA_CLASS_BITS_SMT2),
  BZLA_CLASS_MASK_SMT2 = (BZLA_CLASS_SIZE_SMT2 - 1),

  BZLA_OTHER_TAG_CLASS_SMT2 = 0,

  BZLA_CONSTANT_TAG_CLASS_SMT2 = (BZLA_CLASS_SIZE_SMT2 << 0),
  BZLA_RESERVED_TAG_CLASS_SMT2 = (BZLA_CLASS_SIZE_SMT2 << 1),
  BZLA_COMMAND_TAG_CLASS_SMT2  = (BZLA_CLASS_SIZE_SMT2 << 2),
  BZLA_KEYWORD_TAG_CLASS_SMT2  = (BZLA_CLASS_SIZE_SMT2 << 3),
  BZLA_CORE_TAG_CLASS_SMT2     = (BZLA_CLASS_SIZE_SMT2 << 4),
  BZLA_ARRAY_TAG_CLASS_SMT2    = (BZLA_CLASS_SIZE_SMT2 << 5),
  BZLA_BV_TAG_CLASS_SMT2       = (BZLA_CLASS_SIZE_SMT2 << 6),
  BZLA_FP_TAG_CLASS_SMT2       = (BZLA_CLASS_SIZE_SMT2 << 7),
  BZLA_REAL_TAG_CLASS_SMT2     = (BZLA_CLASS_SIZE_SMT2 << 8),
} BzlaSMT2TagClass;

#define BZLA_TAG_CLASS_MASK_SMT2                              \
  (BZLA_RESERVED_TAG_CLASS_SMT2 | BZLA_COMMAND_TAG_CLASS_SMT2 \
   | BZLA_KEYWORD_TAG_CLASS_SMT2 | BZLA_CORE_TAG_CLASS_SMT2   \
   | BZLA_ARRAY_TAG_CLASS_SMT2 | BZLA_BV_TAG_CLASS_SMT2       \
   | BZLA_FP_TAG_CLASS_SMT2 | BZLA_REAL_TAG_CLASS_SMT2)

typedef enum BzlaSMT2Tag
{
  BZLA_INVALID_TAG_SMT2   = 0 + BZLA_OTHER_TAG_CLASS_SMT2,
  BZLA_PARENT_TAG_SMT2    = 1 + BZLA_OTHER_TAG_CLASS_SMT2,
  BZLA_LPAR_TAG_SMT2      = 2 + BZLA_OTHER_TAG_CLASS_SMT2,
  BZLA_RPAR_TAG_SMT2      = 3 + BZLA_OTHER_TAG_CLASS_SMT2,
  BZLA_SYMBOL_TAG_SMT2    = 4 + BZLA_OTHER_TAG_CLASS_SMT2,
  BZLA_ATTRIBUTE_TAG_SMT2 = 5 + BZLA_OTHER_TAG_CLASS_SMT2,
  BZLA_EXP_TAG_SMT2       = 6 + BZLA_OTHER_TAG_CLASS_SMT2,
  /* <var_binding> */
  BZLA_LETBIND_TAG_SMT2 = 7 + BZLA_OTHER_TAG_CLASS_SMT2,
  /* (<var_binding>+) */
  BZLA_PARLETBINDING_TAG_SMT2 = 8 + BZLA_OTHER_TAG_CLASS_SMT2,
  /* <sorted_var> */
  BZLA_SORTED_VAR_TAG_SMT2 = 9 + BZLA_OTHER_TAG_CLASS_SMT2,
  /* (<sorted_var>+) */
  BZLA_SORTED_VARS_TAG_SMT2 = 10 + BZLA_OTHER_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Constants                                                              */

  BZLA_DECIMAL_CONSTANT_TAG_SMT2     = 0 + BZLA_CONSTANT_TAG_CLASS_SMT2,
  BZLA_HEXADECIMAL_CONSTANT_TAG_SMT2 = 1 + BZLA_CONSTANT_TAG_CLASS_SMT2,
  BZLA_BINARY_CONSTANT_TAG_SMT2      = 2 + BZLA_CONSTANT_TAG_CLASS_SMT2,
  BZLA_STRING_CONSTANT_TAG_SMT2      = 3 + BZLA_CONSTANT_TAG_CLASS_SMT2,
  BZLA_REAL_CONSTANT_TAG_SMT2        = 4 + BZLA_CONSTANT_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Reserved Words                                                         */

  BZLA_PAR_TAG_SMT2                   = 0 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_NUMERAL_RESERVED_WORD_TAG_SMT2 = 1 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_DECIMAL_RESERVED_WORD_TAG_SMT2 = 2 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_STRING_RESERVED_WORD_TAG_SMT2  = 3 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_UNDERSCORE_TAG_SMT2            = 4 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_BANG_TAG_SMT2                  = 5 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_AS_TAG_SMT2                    = 6 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_LET_TAG_SMT2                   = 7 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_FORALL_TAG_SMT2                = 8 + BZLA_RESERVED_TAG_CLASS_SMT2,
  BZLA_EXISTS_TAG_SMT2                = 9 + BZLA_RESERVED_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Commands                                                               */

  BZLA_SET_LOGIC_TAG_SMT2             = 0 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_SET_OPTION_TAG_SMT2            = 1 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_SET_INFO_TAG_SMT2              = 2 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_DECLARE_SORT_TAG_SMT2          = 3 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_DEFINE_SORT_TAG_SMT2           = 4 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_DECLARE_FUN_TAG_SMT2           = 5 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_DEFINE_FUN_TAG_SMT2            = 6 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_DECLARE_CONST_TAG_SMT2         = 7 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_PUSH_TAG_SMT2                  = 8 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_POP_TAG_SMT2                   = 9 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_ASSERT_TAG_SMT2                = 10 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_CHECK_SAT_TAG_SMT2             = 11 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_CHECK_SAT_ASSUMING_TAG_SMT2    = 12 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_ASSERTIONS_TAG_SMT2        = 13 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_ASSIGNMENT_TAG_SMT2        = 14 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_INFO_TAG_SMT2              = 15 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_OPTION_TAG_SMT2            = 16 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_PROOF_TAG_SMT2             = 17 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_UNSAT_ASSUMPTIONS_TAG_SMT2 = 18 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_UNSAT_CORE_TAG_SMT2        = 19 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_VALUE_TAG_SMT2             = 20 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_EXIT_TAG_SMT2                  = 21 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_GET_MODEL_TAG_SMT2             = 22 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_MODEL_TAG_SMT2                 = 23 + BZLA_COMMAND_TAG_CLASS_SMT2,
  BZLA_ECHO_TAG_SMT2                  = 24 + BZLA_COMMAND_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Keywords                                                               */

  BZLA_ALL_STATISTICS_TAG_SMT2            = 0 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_AUTHORS_TAG_SMT2                   = 1 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_AXIOMS_TAG_SMT2                    = 2 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_CHAINABLE_TAG_SMT2                 = 3 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_DEFINITION_TAG_SMT2                = 4 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_DIAG_OUTPUT_CHANNEL_TAG_SMT2       = 5 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_ERROR_BEHAVIOR_TAG_SMT2            = 6 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_EXPAND_DEFINITIONS_TAG_SMT2        = 7 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_EXTENSIONS_TAG_SMT2                = 8 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_FUNS_TAG_SMT2                      = 9 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_FUNS_DESCRIPTION_TAG_SMT2          = 10 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_INTERACTIVE_MODE_TAG_SMT2          = 11 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_PRODUCE_ASSERTIONS_TAG_SMT2        = 12 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_LANGUAGE_TAG_SMT2                  = 13 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_LEFT_ASSOC_TAG_SMT2                = 14 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_NAME_TAG_SMT2                      = 15 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_NAMED_TAG_SMT2                     = 16 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_NOTES_TAG_SMT2                     = 17 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_PRINT_SUCCESS_TAG_SMT2             = 18 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_PRODUCE_ASSIGNMENTS_TAG_SMT2       = 19 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_PRODUCE_MODELS_TAG_SMT2            = 20 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_PRODUCE_PROOFS_TAG_SMT2            = 21 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_PRODUCE_UNSAT_ASSUMPTIONS_TAG_SMT2 = 22 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_PRODUCE_UNSAT_CORES_TAG_SMT2       = 23 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_RANDOM_SEED_TAG_SMT2               = 24 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_REASON_UNKNOWN_TAG_SMT2            = 25 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_REGULAR_OUTPUT_CHANNEL_TAG_SMT2    = 26 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_RIGHT_ASSOC_TAG_SMT2               = 27 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_SORTS_TAG_SMT2                     = 28 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_SORTS_DESCRIPTION_TAG_SMT2         = 29 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_STATUS_TAG_SMT2                    = 30 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_THEORIES_TAG_SMT2                  = 31 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_VALUES_TAG_SMT2                    = 32 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_VERBOSITY_TAG_SMT2                 = 33 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_VERSION_TAG_SMT2                   = 34 + BZLA_KEYWORD_TAG_CLASS_SMT2,
  BZLA_GLOBAL_DECLARATIONS_TAG_SMT2       = 35 + BZLA_KEYWORD_TAG_CLASS_SMT2,

  /* ---------------------------------------------------------------------- */
  /* Theories                                                               */

  /* Core ----------------------------------------------------------------- */
  BZLA_BOOL_TAG_SMT2     = 0 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_TRUE_TAG_SMT2     = 1 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_FALSE_TAG_SMT2    = 2 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_NOT_TAG_SMT2      = 3 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_IMPLIES_TAG_SMT2  = 4 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_AND_TAG_SMT2      = 5 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_OR_TAG_SMT2       = 6 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_XOR_TAG_SMT2      = 7 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_EQUAL_TAG_SMT2    = 8 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_DISTINCT_TAG_SMT2 = 9 + BZLA_CORE_TAG_CLASS_SMT2,
  BZLA_ITE_TAG_SMT2      = 10 + BZLA_CORE_TAG_CLASS_SMT2,

  /* Array ---------------------------------------------------------------- */
  BZLA_ARRAY_TAG_SMT2        = 0 + BZLA_ARRAY_TAG_CLASS_SMT2,
  BZLA_ARRAY_SELECT_TAG_SMT2 = 1 + BZLA_ARRAY_TAG_CLASS_SMT2,
  BZLA_ARRAY_STORE_TAG_SMT2  = 2 + BZLA_ARRAY_TAG_CLASS_SMT2,

  /* Bit-Vectors ---------------------------------------------------------- */
  BZLA_BV_BITVEC_TAG_SMT2       = 0 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_CONCAT_TAG_SMT2       = 1 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_EXTRACT_TAG_SMT2      = 2 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_NOT_TAG_SMT2          = 3 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_NEG_TAG_SMT2          = 4 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_AND_TAG_SMT2          = 5 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_OR_TAG_SMT2           = 6 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_ADD_TAG_SMT2          = 7 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_MUL_TAG_SMT2          = 8 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_UDIV_TAG_SMT2         = 9 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_UREM_TAG_SMT2         = 10 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SHL_TAG_SMT2          = 11 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_LSHR_TAG_SMT2         = 12 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_ULT_TAG_SMT2          = 13 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_NAND_TAG_SMT2         = 14 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_NOR_TAG_SMT2          = 15 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_XOR_TAG_SMT2          = 16 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_XNOR_TAG_SMT2         = 17 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_COMP_TAG_SMT2         = 18 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SUB_TAG_SMT2          = 19 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SDIV_TAG_SMT2         = 20 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SREM_TAG_SMT2         = 21 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SMOD_TAG_SMT2         = 22 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_ASHR_TAG_SMT2         = 23 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_REPEAT_TAG_SMT2       = 24 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_ZERO_EXTEND_TAG_SMT2  = 25 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SIGN_EXTEND_TAG_SMT2  = 26 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_ROTATE_LEFT_TAG_SMT2  = 27 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_ROTATE_RIGHT_TAG_SMT2 = 28 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_ULE_TAG_SMT2          = 29 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_UGT_TAG_SMT2          = 30 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_UGE_TAG_SMT2          = 31 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SLT_TAG_SMT2          = 32 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SLE_TAG_SMT2          = 33 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SGT_TAG_SMT2          = 34 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SGE_TAG_SMT2          = 35 + BZLA_BV_TAG_CLASS_SMT2,
  /* Bitwuzla extensions */
  BZLA_BV_REDOR_TAG_SMT2  = 36 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_REDAND_TAG_SMT2 = 37 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_REDXOR_TAG_SMT2 = 38 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SADDO_TAG_SMT2  = 39 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_UADDO_TAG_SMT2  = 40 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SDIVO_TAG_SMT2  = 41 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SMULO_TAG_SMT2  = 42 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_UMULO_TAG_SMT2  = 43 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_SSUBO_TAG_SMT2  = 44 + BZLA_BV_TAG_CLASS_SMT2,
  BZLA_BV_USUBO_TAG_SMT2  = 45 + BZLA_BV_TAG_CLASS_SMT2,

  /* Theory of Floating Point Numbers ------------------------------------- */
  BZLA_FP_FLOATINGPOINT_TAG_SMT2                = 0 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_FLOAT16_TAG_SMT2                      = 1 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_FLOAT32_TAG_SMT2                      = 2 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_FLOAT64_TAG_SMT2                      = 3 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_FLOAT128_TAG_SMT2                     = 4 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_TAG_SMT2                 = 5 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_NEAREST_TO_EVEN_TAG_SMT2 = 6 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_NEAREST_TO_AWAY_TAG_SMT2 = 7 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_TOWARD_POSITIVE_TAG_SMT2 = 8 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_TOWARD_NEGATIVE_TAG_SMT2 = 9 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_TOWARD_ZERO_TAG_SMT2     = 10 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_RNE_TAG_SMT2             = 11 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_RNA_TAG_SMT2             = 12 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_RTP_TAG_SMT2             = 13 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_RTN_TAG_SMT2             = 14 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUNDINGMODE_RTZ_TAG_SMT2             = 15 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_FP_TAG_SMT2                           = 16 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_POS_ZERO_TAG_SMT2                     = 17 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_NEG_ZERO_TAG_SMT2                     = 18 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_POS_INF_TAG_SMT2                      = 19 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_NEG_INF_TAG_SMT2                      = 20 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_NAN_TAG_SMT2                          = 21 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ABS_TAG_SMT2                          = 22 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_NEG_TAG_SMT2                          = 23 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ADD_TAG_SMT2                          = 24 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_SUB_TAG_SMT2                          = 25 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_MUL_TAG_SMT2                          = 26 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_DIV_TAG_SMT2                          = 27 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_FMA_TAG_SMT2                          = 28 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_SQRT_TAG_SMT2                         = 29 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_REM_TAG_SMT2                          = 30 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_ROUND_TO_INT_TAG_SMT2                 = 31 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_MIN_TAG_SMT2                          = 32 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_MAX_TAG_SMT2                          = 33 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_LEQ_TAG_SMT2                          = 34 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_LT_TAG_SMT2                           = 35 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_GEQ_TAG_SMT2                          = 36 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_GT_TAG_SMT2                           = 37 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_EQ_TAG_SMT2                           = 38 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_IS_NORMAL_TAG_SMT2                    = 39 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_IS_SUBNORMAL_TAG_SMT2                 = 40 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_IS_ZERO_TAG_SMT2                      = 41 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_IS_INF_TAG_SMT2                       = 42 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_IS_NAN_TAG_SMT2                       = 43 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_IS_NEG_TAG_SMT2                       = 44 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_IS_POS_TAG_SMT2                       = 45 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_TO_FP_TAG_SMT2                        = 46 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_TO_FP_UNSIGNED_TAG_SMT2               = 47 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_TO_UBV_TAG_SMT2                       = 48 + BZLA_FP_TAG_CLASS_SMT2,
  BZLA_FP_TO_SBV_TAG_SMT2                       = 49 + BZLA_FP_TAG_CLASS_SMT2,

  /* Reals (for to_fp conversion) ----------------------------------------- */
  BZLA_REAL_DIV_TAG_SMT2 = 0 + BZLA_REAL_TAG_CLASS_SMT2,

} BzlaSMT2Tag;

typedef struct BzlaSMT2Coo
{
  int32_t x, y;
} BzlaSMT2Coo;

typedef struct BzlaSMT2Node
{
  BzlaSMT2Tag tag;
  uint32_t bound : 1;
  uint32_t sort : 1;
  uint32_t scope_level;
  BzlaSMT2Coo coo;
  char *name;
  const BitwuzlaTerm *exp;
  const BitwuzlaSort *sort_alias;
  struct BzlaSMT2Node *next;
} BzlaSMT2Node;

typedef struct BzlaSMT2Item
{
  BzlaSMT2Tag tag;
  BzlaSMT2Coo coo;
  union
  {
    uint32_t num;
    struct
    {
      uint32_t idx0, idx1;
    };
  };
  union
  {
    BzlaSMT2Node *node;
    const BitwuzlaTerm *exp;
    const BitwuzlaSort *sort;
    char *str;
  };
  char *strs[2];
} BzlaSMT2Item;

BZLA_DECLARE_STACK(BzlaSMT2Item, BzlaSMT2Item);
BZLA_DECLARE_STACK(BzlaSMT2NodePtr, BzlaSMT2Node *);

/*------------------------------------------------------------------------*/

static const char *bzla_printable_ascii_chars_smt2 =
    "!\"#$%&'()*+,-./"
    "0123456789"
    ":;<=>?@"
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "[\\]^_`"
    "abcdefghijklmnopqrstuvwxyz"
    "{|}~"
    " \t\r\n";

static const char *bzla_letters_smt2 =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz";

static const char *bzla_decimal_digits_smt2 = "0123456789";

static const char *bzla_hexadecimal_digits_smt2 = "0123456789abcdefABCDEF";

static const char *bzla_extra_symbol_chars_smt2 = "+-/*=%?!.$_~&^<>@";

static const char *bzla_extra_keyword_chars_smt2 = "+-/*=%?!.$_~&^<>@";

typedef enum BzlaSMT2CharClass
{
  BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2     = (1 << 0),
  BZLA_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2 = (1 << 1),
  BZLA_STRING_CHAR_CLASS_SMT2            = (1 << 2),
  BZLA_SYMBOL_CHAR_CLASS_SMT2            = (1 << 3),
  BZLA_QUOTED_SYMBOL_CHAR_CLASS_SMT2     = (1 << 4),
  BZLA_KEYWORD_CHAR_CLASS_SMT2           = (1 << 5),
} BzlaSMT2CharClass;

typedef struct BzlaSMT2Parser
{
  Bitwuzla *bitwuzla;
  BzlaMemMgr *mem;
  bool done;
  bool need_arrays;
  bool need_functions;
  bool need_quantifiers;
  bool saved;
  int32_t savedch;
  int32_t last_end_of_line_ycoo;
  int32_t open;
  uint32_t nprefix;
  int32_t sorted_var;
  bool isvarbinding;
  const char *expecting_body;
  char *error;
  char *logic;
  unsigned char cc[256];
  FILE *infile;
  char *infile_name;
  FILE *outfile;
  double parse_start;
  bool store_tokens; /* needed for parsing terms in get-value */
  BzlaIntStack *prefix;
  BzlaCharStack token, tokens;
  BitwuzlaSortConstPtrStack sorts;
  BzlaSMT2ItemStack work;
  BzlaSMT2Coo coo, lastcoo, nextcoo, perrcoo;
  BzlaSMT2Node *last_node;
  BzlaParseResult *res;
  BitwuzlaTermConstPtrStack sat_assuming_assumptions;
  uint32_t scope_level;
  struct
  {
    uint32_t size, count;
    BzlaSMT2Node **table;
  } symbol;
  struct
  {
    int32_t all, set_logic, asserts, check_sat, exits, model;
  } commands;

  /* SMT2 options */
  bool print_success;
  bool global_declarations;

  bool track_mode_set;
} BzlaSMT2Parser;

/*------------------------------------------------------------------------*/

static void
configure_smt_comp_mode(BzlaSMT2Parser *parser)
{
  const char *track  = 0;
  Bitwuzla *bitwuzla = parser->bitwuzla;

  if (parser->track_mode_set
      || !bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_SMT_COMP_MODE))
    return;

  bitwuzla_set_option(
      bitwuzla, BITWUZLA_OPT_PP_BETA_REDUCE, BZLA_BETA_REDUCE_FUN);

  /* incremental track */
  if (parser->print_success || parser->scope_level > 0)
  {
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_DECLSORT_BV_WIDTH, 16);
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_INCREMENTAL, 1);
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PP_NONDESTR_SUBST, 1);
    track = "incremental";
  }
  /* unsat core track */
  else if (bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_PRODUCE_UNSAT_CORES))
  {
    track = "unsat core";
  }
  /* single query track, model validation track */
  else
  {
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_DECLSORT_BV_WIDTH, 16);
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PP_NORMALIZE_ADD, 1);

    if (!strcmp(parser->logic, "QF_BV"))
    {
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_FUN_PREPROP, 1);
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PROP_CONST_BITS, 1);
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PROP_INFER_INEQ_BOUNDS, 1);
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PROP_NPROPS, 10000);
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PROP_NUPDATES, 2000000);
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PROP_PROB_RANDOM_INPUT, 10);
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PROP_SEXT, 1);
      bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PROP_USE_INV_LT_CONCAT, 1);
    }

    if (bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS))
    {
      track = "model validation";
    }
    else
    {
      track = "single query";
    }
  }
  BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
           1,
           "SMT-COMP mode: Configured for %s track",
           track);
  parser->track_mode_set = true;
}

/*------------------------------------------------------------------------*/

static int32_t
xcoo_smt2(BzlaSMT2Parser *parser)
{
  return parser->perrcoo.x ? parser->perrcoo.x : parser->coo.x;
}

static int32_t
ycoo_smt2(BzlaSMT2Parser *parser)
{
  return parser->perrcoo.x ? parser->perrcoo.y : parser->coo.y;
}

static char *
perr_smt2(BzlaSMT2Parser *parser, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;
  if (!parser->error)
  {
    va_start(ap, fmt);
    bytes = bzla_mem_parse_error_msg_length(parser->infile_name, fmt, ap);
    va_end(ap);
    va_start(ap, fmt);
    parser->error = bzla_mem_parse_error_msg(parser->mem,
                                             parser->infile_name,
                                             xcoo_smt2(parser),
                                             ycoo_smt2(parser),
                                             fmt,
                                             ap,
                                             bytes);
    va_end(ap);
  }
  return parser->error;
}

static void
savech_smt2(BzlaSMT2Parser *parser, int32_t ch)
{
  assert(!parser->saved);
  parser->saved   = true;
  parser->savedch = ch;
  if (ch == '\n')
  {
    assert(parser->nextcoo.x > 1);
    parser->nextcoo.x--;
    parser->nextcoo.y = parser->last_end_of_line_ycoo;
  }
  else
  {
    assert(parser->nextcoo.y > 1);
    parser->nextcoo.y--;
  }
}

static char *
cerr_smt2(BzlaSMT2Parser *parser, const char *p, int32_t ch, const char *s)
{
  const char *d, *n;

  if (!parser->saved) savech_smt2(parser, ch);
  parser->perrcoo = parser->nextcoo;

  if (ch == EOF)
    return perr_smt2(
        parser, "%s end-of-file%s%s", p, (s ? " " : ""), (s ? s : ""));
  if (isprint(ch) && ch != '\\')
    return perr_smt2(
        parser, "%s character '%c'%s%s", p, ch, (s ? " " : ""), (s ? s : ""));

  switch (ch)
  {
    case '\\':
      n = "backslash";
      d = "\\";
      break;
    case '\n':
      n = "new line";
      d = "\\n";
      break;
    case '\t':
      n = "horizontal tabulator";
      d = "\\t";
      break;
    case '\r':
      n = "carriage return";
      d = "\\r";
      break;
    default:
      n = "character";
      d = 0;
      break;
  }

  if (d)
    return perr_smt2(
        parser, "%s %s '%s'%s%s", p, n, d, (s ? " " : ""), (s ? s : ""));

  return perr_smt2(parser,
                   "%s (non-printable) character (code %d)%s%s",
                   p,
                   ch,
                   (s ? " " : ""),
                   (s ? s : ""));
}

static uint32_t bzla_primes_smt2[] = {
    1000000007u, 2000000011u, 3000000019u, 4000000007u};

#define BZLA_NPRIMES_SMT2 (sizeof bzla_primes_smt2 / sizeof *bzla_primes_smt2)

static uint32_t
hash_name_smt2(BzlaSMT2Parser *parser, const char *name)
{
  uint32_t res = 0, i = 0;
  size_t len, pos     = 0;

  /* Ignore pipes in quoted symbols. Symbol |x| and x should have the same hash
   * value. */
  len = strlen(name);
  if (name[0] == '|' && name[len - 1] == '|')
  {
    pos = 1;
    len -= 1;
  }
  for (; pos < len; pos++)
  {
    res += name[pos];
    res *= bzla_primes_smt2[i++];
    if (i == BZLA_NPRIMES_SMT2) i = 0;
  }
  return res & (parser->symbol.size - 1);
}

static int32_t
nextch_smt2(BzlaSMT2Parser *parser)
{
  int32_t res;
  if (parser->saved)
    res = parser->savedch, parser->saved = false;
  else if (parser->prefix
           && parser->nprefix < BZLA_COUNT_STACK(*parser->prefix))
    res = parser->prefix->start[parser->nprefix++];
  else
    res = getc(parser->infile);
  if (res == '\n')
  {
    parser->nextcoo.x++;
    assert(parser->nextcoo.x > 0);
    parser->last_end_of_line_ycoo = parser->nextcoo.y;
    parser->nextcoo.y             = 1;
  }
  else
    parser->nextcoo.y++, assert(parser->nextcoo.y > 0);
  return res;
}

static void
enlarge_symbol_table_smt2(BzlaSMT2Parser *parser)
{
  uint32_t old_size        = parser->symbol.size;
  uint32_t new_size        = old_size ? 2 * old_size : 1;
  BzlaSMT2Node **old_table = parser->symbol.table, *p, **q;
  BzlaSMT2NodePtrStack chain;
  uint32_t h, i;
  BZLA_CNEWN(parser->mem, parser->symbol.table, new_size);
  parser->symbol.size = new_size;

  /* Note: A symbol can occur multiple times in the collision chain due to
   *       shadowing of symbols in binders. Thus, it's important that the
   *       order of the symbols stays the same. Otherwise, find_symbol_smt2
   *       won't find the correct symbol for the current scope. */
  BZLA_INIT_STACK(parser->mem, chain);
  for (i = 0; i < old_size; i++)
  {
    for (p = old_table[i]; p; p = p->next)
    {
      BZLA_PUSH_STACK(chain, p);
    }
    while (!BZLA_EMPTY_STACK(chain))
    {
      p       = BZLA_POP_STACK(chain);
      h       = hash_name_smt2(parser, p->name);
      p->next = *(q = parser->symbol.table + h);
      *q      = p;
    }
  }
  BZLA_RELEASE_STACK(chain);
  BZLA_DELETEN(parser->mem, old_table, old_size);
}

static BzlaSMT2Node *
find_symbol_smt2(BzlaSMT2Parser *parser, const char *name)
{
  unsigned h;
  BzlaSMT2Node *s;
  size_t len_name, len_s;
  bool name_quoted, s_quoted;

  if (parser->symbol.size == 0) return 0;

  len_name    = strlen(name);
  name_quoted = name[0] == '|' && name[len_name - 1] == '|';

  h = hash_name_smt2(parser, name);
  for (s = parser->symbol.table[h]; s; s = s->next)
  {
    len_s    = strlen(s->name);
    s_quoted = s->name[0] == '|' && s->name[len_s - 1] == '|';

    if (s_quoted == name_quoted)
    {
      if (!strcmp(s->name, name))
      {
        break;
      }
    }
    /* Check if 's' is quoted but 'name' is not quoted. */
    else if (s_quoted)
    {
      if (len_s - 2 == len_name && !strncmp(s->name + 1, name, len_name))
      {
        break;
      }
    }
    /* Check if 'name' is quoted but 's' is not quoted. */
    else if (name_quoted)
    {
      if (len_name - 2 == len_s && !strncmp(s->name, name + 1, len_s))
      {
        break;
      }
    }
  }
  return s;
}

static void
insert_symbol_smt2(BzlaSMT2Parser *parser, BzlaSMT2Node *symbol)
{
  unsigned h;
  BzlaSMT2Node *p;

  if (parser->symbol.size <= parser->symbol.count)
    enlarge_symbol_table_smt2(parser);

  /* always add new symbol as first element to collision chain (required for
   * scoping) */
  h = hash_name_smt2(parser, symbol->name);
  p = parser->symbol.table[h];

  parser->symbol.table[h] = symbol;
  symbol->next            = p;
  parser->symbol.count++;
  assert(parser->symbol.count > 0);
  BZLA_MSG(bitwuzla_get_bzla_msg(parser->bitwuzla),
           2,
           "insert symbol '%s' at scope level %u",
           symbol->name,
           parser->scope_level);
}

static BzlaSMT2Node *
new_node_smt2(BzlaSMT2Parser *parser, BzlaSMT2Tag tag)
{
  BzlaSMT2Node *res;
  BZLA_CNEW(parser->mem, res);
  res->tag         = tag;
  res->scope_level = parser->scope_level;
  return res;
}

static void
release_symbol_smt2(BzlaSMT2Parser *parser, BzlaSMT2Node *symbol)
{
  assert(symbol->tag != BZLA_PARENT_TAG_SMT2);
  bzla_mem_freestr(parser->mem, symbol->name);
  BZLA_DELETE(parser->mem, symbol);
}

static void
remove_symbol_smt2(BzlaSMT2Parser *parser, BzlaSMT2Node *symbol)
{
  BzlaSMT2Node **p, *s;
  unsigned h;

  BZLA_MSG(bitwuzla_get_bzla_msg(parser->bitwuzla),
           2,
           "remove symbol '%s' at scope level %u",
           symbol->name,
           parser->scope_level);

  h = hash_name_smt2(parser, symbol->name);
  for (p = parser->symbol.table + h;
       (s = *p) && (strcmp(s->name, symbol->name) || s != symbol);
       p = &s->next)
    ;
  assert(*p == symbol);
  *p = symbol->next;
  release_symbol_smt2(parser, symbol);
  assert(parser->symbol.count > 0);
  parser->symbol.count--;
}

static void
release_symbols_smt2(BzlaSMT2Parser *parser)
{
  BzlaSMT2Node *p, *next;
  uint32_t i;
  for (i = 0; i < parser->symbol.size; i++)
    for (p = parser->symbol.table[i]; p; p = next)
      next = p->next, release_symbol_smt2(parser, p);

  BZLA_DELETEN(parser->mem, parser->symbol.table, parser->symbol.size);
}

static void
release_item_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *item)
{
  if (item->strs[0]) bzla_mem_freestr(parser->mem, item->strs[0]);
  if (item->strs[1]) bzla_mem_freestr(parser->mem, item->strs[1]);
  if (item->tag != BZLA_EXP_TAG_SMT2
      && (item->tag & BZLA_CONSTANT_TAG_CLASS_SMT2))
  {
    bzla_mem_freestr(parser->mem, item->str);
  }
}

static void
open_new_scope(BzlaSMT2Parser *parser)
{
  parser->scope_level++;

  BZLA_MSG(bitwuzla_get_bzla_msg(parser->bitwuzla),
           2,
           "opened new scope at level %d",
           parser->scope_level);
}

static void
close_current_scope(BzlaSMT2Parser *parser)
{
  double start;
  uint32_t i;
  BzlaSMT2Node *node, *next;

  start = bzla_util_time_stamp();

  if (!parser->global_declarations)
  {
    /* delete symbols from current scope */
    for (i = 0; i < parser->symbol.size; i++)
    {
      node = parser->symbol.table[i];
      while (node)
      {
        next = node->next;
        if (node->scope_level == parser->scope_level)
          remove_symbol_smt2(parser, node);
        node = next;
      }
    }
  }

  BZLA_MSG(bitwuzla_get_bzla_msg(parser->bitwuzla),
           2,
           "closed scope at level %d in %.3f seconds",
           parser->scope_level,
           bzla_util_time_stamp() - start);
  parser->scope_level--;
}

static void
init_char_classes_smt2(BzlaSMT2Parser *parser)
{
  unsigned char *cc = parser->cc;
  const char *p;

  BZLA_CLRN(cc, 256);

  for (p = bzla_decimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2;

  for (p = bzla_hexadecimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2;

  for (p = bzla_printable_ascii_chars_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_STRING_CHAR_CLASS_SMT2;

  for (p = bzla_letters_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_SYMBOL_CHAR_CLASS_SMT2;
  for (p = bzla_decimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_SYMBOL_CHAR_CLASS_SMT2;
  for (p = bzla_extra_symbol_chars_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_SYMBOL_CHAR_CLASS_SMT2;

  for (p = bzla_printable_ascii_chars_smt2; *p; p++)
    if (*p != '\\' && *p != '|')
      cc[(unsigned char) *p] |= BZLA_QUOTED_SYMBOL_CHAR_CLASS_SMT2;

  for (p = bzla_letters_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_KEYWORD_CHAR_CLASS_SMT2;
  for (p = bzla_decimal_digits_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_KEYWORD_CHAR_CLASS_SMT2;
  for (p = bzla_extra_keyword_chars_smt2; *p; p++)
    cc[(unsigned char) *p] |= BZLA_KEYWORD_CHAR_CLASS_SMT2;
}

#define INSERT(STR, TAG)                                      \
  do                                                          \
  {                                                           \
    BzlaSMT2Node *NODE = new_node_smt2(parser, (TAG));        \
    NODE->name         = bzla_mem_strdup(parser->mem, (STR)); \
    assert(!find_symbol_smt2(parser, NODE->name));            \
    insert_symbol_smt2(parser, NODE);                         \
  } while (0)

static void
insert_keywords_smt2(BzlaSMT2Parser *parser)
{
  INSERT(":all-statistics", BZLA_ALL_STATISTICS_TAG_SMT2);
  INSERT(":authors", BZLA_AUTHORS_TAG_SMT2);
  INSERT(":axioms", BZLA_AXIOMS_TAG_SMT2);
  INSERT(":chainable", BZLA_CHAINABLE_TAG_SMT2);
  INSERT(":definition", BZLA_DEFINITION_TAG_SMT2);
  INSERT(":diagnostic-output-channel", BZLA_DIAG_OUTPUT_CHANNEL_TAG_SMT2);
  INSERT(":error-behavior", BZLA_ERROR_BEHAVIOR_TAG_SMT2);
  INSERT(":expand-definitions", BZLA_EXPAND_DEFINITIONS_TAG_SMT2);
  INSERT(":extensions", BZLA_EXTENSIONS_TAG_SMT2);
  INSERT(":funs", BZLA_FUNS_TAG_SMT2);
  INSERT(":funs-description", BZLA_FUNS_DESCRIPTION_TAG_SMT2);
  INSERT(":interactive-mode", BZLA_INTERACTIVE_MODE_TAG_SMT2);
  INSERT(":produce-assertions", BZLA_PRODUCE_ASSERTIONS_TAG_SMT2);
  INSERT(":language", BZLA_LANGUAGE_TAG_SMT2);
  INSERT(":left-assoc", BZLA_LEFT_ASSOC_TAG_SMT2);
  INSERT(":name", BZLA_NAME_TAG_SMT2);
  INSERT(":named", BZLA_NAMED_TAG_SMT2);
  INSERT(":notes", BZLA_NOTES_TAG_SMT2);
  INSERT(":print-success", BZLA_PRINT_SUCCESS_TAG_SMT2);
  INSERT(":produce-assignments", BZLA_PRODUCE_ASSIGNMENTS_TAG_SMT2);
  INSERT(":produce-models", BZLA_PRODUCE_MODELS_TAG_SMT2);
  INSERT(":produce-proofs", BZLA_PRODUCE_PROOFS_TAG_SMT2);
  INSERT(":produce-unsat-assumptions", BZLA_PRODUCE_UNSAT_ASSUMPTIONS_TAG_SMT2);
  INSERT(":produce-unsat-cores", BZLA_PRODUCE_UNSAT_CORES_TAG_SMT2);
  INSERT(":random-seed", BZLA_RANDOM_SEED_TAG_SMT2);
  INSERT(":reason-unknown", BZLA_REASON_UNKNOWN_TAG_SMT2);
  INSERT(":regular-output-channel", BZLA_REGULAR_OUTPUT_CHANNEL_TAG_SMT2);
  INSERT(":right-assoc", BZLA_RIGHT_ASSOC_TAG_SMT2);
  INSERT(":sorts", BZLA_SORTS_TAG_SMT2);
  INSERT(":sorts-description", BZLA_SORTS_DESCRIPTION_TAG_SMT2);
  INSERT(":status", BZLA_STATUS_TAG_SMT2);
  INSERT(":theories", BZLA_THEORIES_TAG_SMT2);
  INSERT(":values", BZLA_VALUES_TAG_SMT2);
  INSERT(":verbosity", BZLA_VERBOSITY_TAG_SMT2);
  INSERT(":version", BZLA_VERSION_TAG_SMT2);
  INSERT(":global-declarations", BZLA_GLOBAL_DECLARATIONS_TAG_SMT2);
}

static void
insert_reserved_words_smt2(BzlaSMT2Parser *parser)
{
  INSERT("!", BZLA_BANG_TAG_SMT2);
  INSERT("_", BZLA_UNDERSCORE_TAG_SMT2);
  INSERT("as", BZLA_AS_TAG_SMT2);
  INSERT("DECIMAL", BZLA_DECIMAL_RESERVED_WORD_TAG_SMT2);
  INSERT("exists", BZLA_EXISTS_TAG_SMT2);
  INSERT("forall", BZLA_FORALL_TAG_SMT2);
  INSERT("let", BZLA_LET_TAG_SMT2);
  INSERT("par", BZLA_PAR_TAG_SMT2);
  INSERT("STRING", BZLA_STRING_RESERVED_WORD_TAG_SMT2);
}

static void
insert_commands_smt2(BzlaSMT2Parser *parser)
{
  INSERT("assert", BZLA_ASSERT_TAG_SMT2);
  INSERT("check-sat", BZLA_CHECK_SAT_TAG_SMT2);
  INSERT("check-sat-assuming", BZLA_CHECK_SAT_ASSUMING_TAG_SMT2);
  INSERT("declare-sort", BZLA_DECLARE_SORT_TAG_SMT2);
  INSERT("declare-fun", BZLA_DECLARE_FUN_TAG_SMT2);
  INSERT("declare-const", BZLA_DECLARE_CONST_TAG_SMT2);
  INSERT("define-sort", BZLA_DEFINE_SORT_TAG_SMT2);
  INSERT("define-fun", BZLA_DEFINE_FUN_TAG_SMT2);
  INSERT("echo", BZLA_ECHO_TAG_SMT2);
  INSERT("exit", BZLA_EXIT_TAG_SMT2);
  INSERT("get-model", BZLA_GET_MODEL_TAG_SMT2);
  INSERT("get-assertions", BZLA_GET_ASSERTIONS_TAG_SMT2);
  INSERT("get-assignment", BZLA_GET_ASSIGNMENT_TAG_SMT2);
  INSERT("get-info", BZLA_GET_INFO_TAG_SMT2);
  INSERT("get-option", BZLA_GET_OPTION_TAG_SMT2);
  INSERT("get-proof", BZLA_GET_PROOF_TAG_SMT2);
  INSERT("get-unsat-core", BZLA_GET_UNSAT_CORE_TAG_SMT2);
  INSERT("get-unsat-assumptions", BZLA_GET_UNSAT_ASSUMPTIONS_TAG_SMT2);
  INSERT("get-value", BZLA_GET_VALUE_TAG_SMT2);
  INSERT("model", BZLA_MODEL_TAG_SMT2);
  INSERT("pop", BZLA_POP_TAG_SMT2);
  INSERT("push", BZLA_PUSH_TAG_SMT2);
  INSERT("set-logic", BZLA_SET_LOGIC_TAG_SMT2);
  INSERT("set-info", BZLA_SET_INFO_TAG_SMT2);
  INSERT("set-option", BZLA_SET_OPTION_TAG_SMT2);
}

static void
insert_core_symbols_smt2(BzlaSMT2Parser *parser)
{
  INSERT("Bool", BZLA_BOOL_TAG_SMT2);
  INSERT("true", BZLA_TRUE_TAG_SMT2);
  INSERT("false", BZLA_FALSE_TAG_SMT2);
  INSERT("not", BZLA_NOT_TAG_SMT2);
  INSERT("=>", BZLA_IMPLIES_TAG_SMT2);
  INSERT("and", BZLA_AND_TAG_SMT2);
  INSERT("or", BZLA_OR_TAG_SMT2);
  INSERT("xor", BZLA_XOR_TAG_SMT2);
  INSERT("=", BZLA_EQUAL_TAG_SMT2);
  INSERT("distinct", BZLA_DISTINCT_TAG_SMT2);
  INSERT("ite", BZLA_ITE_TAG_SMT2);
}

static void
insert_array_symbols_smt2(BzlaSMT2Parser *parser)
{
  INSERT("Array", BZLA_ARRAY_TAG_SMT2);
  INSERT("select", BZLA_ARRAY_SELECT_TAG_SMT2);
  INSERT("store", BZLA_ARRAY_STORE_TAG_SMT2);
}

static void
insert_bitvec_symbols_smt2(BzlaSMT2Parser *parser)
{
  INSERT("BitVec", BZLA_BV_BITVEC_TAG_SMT2);
  INSERT("concat", BZLA_BV_CONCAT_TAG_SMT2);
  INSERT("extract", BZLA_BV_EXTRACT_TAG_SMT2);
  INSERT("bvnot", BZLA_BV_NOT_TAG_SMT2);
  INSERT("bvneg", BZLA_BV_NEG_TAG_SMT2);
  INSERT("bvand", BZLA_BV_AND_TAG_SMT2);
  INSERT("bvor", BZLA_BV_OR_TAG_SMT2);
  INSERT("bvadd", BZLA_BV_ADD_TAG_SMT2);
  INSERT("bvmul", BZLA_BV_MUL_TAG_SMT2);
  INSERT("bvudiv", BZLA_BV_UDIV_TAG_SMT2);
  INSERT("bvurem", BZLA_BV_UREM_TAG_SMT2);
  INSERT("bvshl", BZLA_BV_SHL_TAG_SMT2);
  INSERT("bvlshr", BZLA_BV_LSHR_TAG_SMT2);
  INSERT("bvult", BZLA_BV_ULT_TAG_SMT2);
  INSERT("bvnand", BZLA_BV_NAND_TAG_SMT2);
  INSERT("bvnor", BZLA_BV_NOR_TAG_SMT2);
  INSERT("bvxor", BZLA_BV_XOR_TAG_SMT2);
  INSERT("bvxnor", BZLA_BV_XNOR_TAG_SMT2);
  INSERT("bvcomp", BZLA_BV_COMP_TAG_SMT2);
  INSERT("bvsub", BZLA_BV_SUB_TAG_SMT2);
  INSERT("bvsdiv", BZLA_BV_SDIV_TAG_SMT2);
  INSERT("bvsrem", BZLA_BV_SREM_TAG_SMT2);
  INSERT("bvsmod", BZLA_BV_SMOD_TAG_SMT2);
  INSERT("bvashr", BZLA_BV_ASHR_TAG_SMT2);
  INSERT("repeat", BZLA_BV_REPEAT_TAG_SMT2);
  INSERT("zero_extend", BZLA_BV_ZERO_EXTEND_TAG_SMT2);
  INSERT("sign_extend", BZLA_BV_SIGN_EXTEND_TAG_SMT2);
  INSERT("rotate_left", BZLA_BV_ROTATE_LEFT_TAG_SMT2);
  INSERT("rotate_right", BZLA_BV_ROTATE_RIGHT_TAG_SMT2);
  INSERT("bvule", BZLA_BV_ULE_TAG_SMT2);
  INSERT("bvugt", BZLA_BV_UGT_TAG_SMT2);
  INSERT("bvuge", BZLA_BV_UGE_TAG_SMT2);
  INSERT("bvslt", BZLA_BV_SLT_TAG_SMT2);
  INSERT("bvsle", BZLA_BV_SLE_TAG_SMT2);
  INSERT("bvsgt", BZLA_BV_SGT_TAG_SMT2);
  INSERT("bvsge", BZLA_BV_SGE_TAG_SMT2);
  /* Bitwuzla extensions */
  INSERT("bvredor", BZLA_BV_REDOR_TAG_SMT2);
  INSERT("bvredxor", BZLA_BV_REDXOR_TAG_SMT2);
  INSERT("bvredand", BZLA_BV_REDAND_TAG_SMT2);
  INSERT("bvsaddo", BZLA_BV_SADDO_TAG_SMT2);
  INSERT("bvuaddo", BZLA_BV_UADDO_TAG_SMT2);
  INSERT("bvsdivo", BZLA_BV_SDIVO_TAG_SMT2);
  INSERT("bvsmulo", BZLA_BV_SMULO_TAG_SMT2);
  INSERT("bvumulo", BZLA_BV_UMULO_TAG_SMT2);
  INSERT("bvssubo", BZLA_BV_SSUBO_TAG_SMT2);
  INSERT("bvusubo", BZLA_BV_USUBO_TAG_SMT2);
}

static void
insert_fp_symbols_smt2(BzlaSMT2Parser *parser)
{
  INSERT("FloatingPoint", BZLA_FP_FLOATINGPOINT_TAG_SMT2);
  INSERT("Float16", BZLA_FP_FLOAT16_TAG_SMT2);
  INSERT("Float32", BZLA_FP_FLOAT32_TAG_SMT2);
  INSERT("Float64", BZLA_FP_FLOAT64_TAG_SMT2);
  INSERT("Float128", BZLA_FP_FLOAT128_TAG_SMT2);
  INSERT("RoundingMode", BZLA_FP_ROUNDINGMODE_TAG_SMT2);
  INSERT("roundNearestTiesToEven",
         BZLA_FP_ROUNDINGMODE_NEAREST_TO_EVEN_TAG_SMT2);
  INSERT("roundNearestTiesToAway",
         BZLA_FP_ROUNDINGMODE_NEAREST_TO_AWAY_TAG_SMT2);
  INSERT("roundTowardPositive", BZLA_FP_ROUNDINGMODE_TOWARD_POSITIVE_TAG_SMT2);
  INSERT("roundTowardNegative", BZLA_FP_ROUNDINGMODE_TOWARD_NEGATIVE_TAG_SMT2);
  INSERT("roundTowardZero", BZLA_FP_ROUNDINGMODE_TOWARD_ZERO_TAG_SMT2);
  INSERT("RNE", BZLA_FP_ROUNDINGMODE_RNE_TAG_SMT2);
  INSERT("RNA", BZLA_FP_ROUNDINGMODE_RNA_TAG_SMT2);
  INSERT("RTP", BZLA_FP_ROUNDINGMODE_RTP_TAG_SMT2);
  INSERT("RTN", BZLA_FP_ROUNDINGMODE_RTN_TAG_SMT2);
  INSERT("RTZ", BZLA_FP_ROUNDINGMODE_RTZ_TAG_SMT2);
  INSERT("fp", BZLA_FP_FP_TAG_SMT2);
  INSERT("+zero", BZLA_FP_POS_ZERO_TAG_SMT2);
  INSERT("-zero", BZLA_FP_NEG_ZERO_TAG_SMT2);
  INSERT("+oo", BZLA_FP_POS_INF_TAG_SMT2);
  INSERT("-oo", BZLA_FP_NEG_INF_TAG_SMT2);
  INSERT("NaN", BZLA_FP_NAN_TAG_SMT2);
  INSERT("fp.abs", BZLA_FP_ABS_TAG_SMT2);
  INSERT("fp.neg", BZLA_FP_NEG_TAG_SMT2);
  INSERT("fp.add", BZLA_FP_ADD_TAG_SMT2);
  INSERT("fp.sub", BZLA_FP_SUB_TAG_SMT2);
  INSERT("fp.mul", BZLA_FP_MUL_TAG_SMT2);
  INSERT("fp.div", BZLA_FP_DIV_TAG_SMT2);
  INSERT("fp.fma", BZLA_FP_FMA_TAG_SMT2);
  INSERT("fp.sqrt", BZLA_FP_SQRT_TAG_SMT2);
  INSERT("fp.rem", BZLA_FP_REM_TAG_SMT2);
  INSERT("fp.roundToIntegral", BZLA_FP_ROUND_TO_INT_TAG_SMT2);
  INSERT("fp.min", BZLA_FP_MIN_TAG_SMT2);
  INSERT("fp.max", BZLA_FP_MAX_TAG_SMT2);
  INSERT("fp.leq", BZLA_FP_LEQ_TAG_SMT2);
  INSERT("fp.lt", BZLA_FP_LT_TAG_SMT2);
  INSERT("fp.geq", BZLA_FP_GEQ_TAG_SMT2);
  INSERT("fp.gt", BZLA_FP_GT_TAG_SMT2);
  INSERT("fp.eq", BZLA_FP_EQ_TAG_SMT2);
  INSERT("fp.isNormal", BZLA_FP_IS_NORMAL_TAG_SMT2);
  INSERT("fp.isSubnormal", BZLA_FP_IS_SUBNORMAL_TAG_SMT2);
  INSERT("fp.isZero", BZLA_FP_IS_ZERO_TAG_SMT2);
  INSERT("fp.isInfinite", BZLA_FP_IS_INF_TAG_SMT2);
  INSERT("fp.isNaN", BZLA_FP_IS_NAN_TAG_SMT2);
  INSERT("fp.isNegative", BZLA_FP_IS_NEG_TAG_SMT2);
  INSERT("fp.isPositive", BZLA_FP_IS_POS_TAG_SMT2);
  INSERT("fp.to_ubv", BZLA_FP_TO_UBV_TAG_SMT2);
  INSERT("fp.to_sbv", BZLA_FP_TO_SBV_TAG_SMT2);
  INSERT("to_fp", BZLA_FP_TO_FP_TAG_SMT2);
  INSERT("to_fp_unsigned", BZLA_FP_TO_FP_UNSIGNED_TAG_SMT2);
}

static void
insert_real_symbols_smt2(BzlaSMT2Parser *parser)
{
  INSERT("/", BZLA_REAL_DIV_TAG_SMT2);
}

static BzlaSMT2Parser *
new_smt2_parser(Bitwuzla *bitwuzla)
{
  BzlaSMT2Parser *res;
  BzlaMemMgr *mem = bzla_mem_mgr_new();
  BZLA_CNEW(mem, res);
  res->done          = false;
  res->bitwuzla      = bitwuzla;
  res->mem           = mem;
  res->scope_level   = 0;
  res->print_success = false;
  res->store_tokens  = false;

  BZLA_INIT_STACK(mem, res->work);
  BZLA_INIT_STACK(mem, res->sorts);

  BZLA_INIT_STACK(mem, res->sat_assuming_assumptions);
  BZLA_INIT_STACK(mem, res->token);
  BZLA_INIT_STACK(mem, res->tokens);

  init_char_classes_smt2(res);

  insert_keywords_smt2(res);
  insert_reserved_words_smt2(res);
  insert_commands_smt2(res);
  insert_core_symbols_smt2(res);
  insert_array_symbols_smt2(res);
  insert_bitvec_symbols_smt2(res);
  insert_fp_symbols_smt2(res);
  insert_real_symbols_smt2(res);

  return res;
}

static void
release_work_smt2(BzlaSMT2Parser *parser)
{
  BzlaSMT2Item item;
  while (!BZLA_EMPTY_STACK(parser->work))
  {
    item = BZLA_POP_STACK(parser->work);
    release_item_smt2(parser, &item);
  }
  BZLA_RELEASE_STACK(parser->work);
}

static void
delete_smt2_parser(BzlaSMT2Parser *parser)
{
  BzlaMemMgr *mem = parser->mem;

  while (parser->scope_level) close_current_scope(parser);

  release_symbols_smt2(parser);
  release_work_smt2(parser);

  if (parser->infile_name) bzla_mem_freestr(mem, parser->infile_name);
  if (parser->error) bzla_mem_freestr(mem, parser->error);
  if (parser->logic) bzla_mem_freestr(mem, parser->logic);

  BZLA_RELEASE_STACK(parser->sorts);

  BZLA_RELEASE_STACK(parser->sat_assuming_assumptions);
  BZLA_RELEASE_STACK(parser->token);
  BZLA_RELEASE_STACK(parser->tokens);

  BZLA_DELETE(mem, parser);
  bzla_mem_mgr_delete(mem);
}

static bool
isspace_smt2(int32_t ch)
{
  return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

static uint32_t
cc_smt2(BzlaSMT2Parser *parser, int32_t ch)
{
  if (ch < 0 || ch >= 256) return 0;
  return parser->cc[(unsigned char) ch];
}

/* this is only needed for storing the parsed tokens for get-value */
static void
storech_smt2(BzlaSMT2Parser *parser, int32_t ch)
{
  char t;
  if (!parser->store_tokens) return;

  t = BZLA_EMPTY_STACK(parser->tokens) ? 0 : BZLA_TOP_STACK(parser->tokens);
  if (!ch && t == '(') return;
  if (ch == ')' && t == ' ')
  {
    (void) BZLA_POP_STACK(parser->tokens);
  }
  BZLA_PUSH_STACK(parser->tokens, ch ? ch : ' ');
}

static void
pushch_smt2(BzlaSMT2Parser *parser, int32_t ch)
{
  assert(ch != EOF);
  BZLA_PUSH_STACK(parser->token, ch);
  storech_smt2(parser, ch);
}

static int32_t
read_token_aux_smt2(BzlaSMT2Parser *parser)
{
  BzlaSMT2Node *node;
  unsigned char cc;
  int32_t ch, res_tag;
  assert(!BZLA_INVALID_TAG_SMT2);  // error code:          0
  BZLA_RESET_STACK(parser->token);
  parser->last_node = 0;
RESTART:
  do
  {
    parser->coo = parser->nextcoo;
    if ((ch = nextch_smt2(parser)) == EOF)
    {
      assert(EOF < 0);
      return EOF;  // end of tokens:       EOF
    }
  } while (isspace_smt2(ch));
  if (ch == ';')
  {
    while ((ch = nextch_smt2(parser)) != '\n')
      if (ch == EOF)
      {
        assert(!BZLA_INVALID_TAG_SMT2);
        return !perr_smt2(parser, "unexpected end-of-file in comment");
      }
    goto RESTART;
  }
  cc = cc_smt2(parser, ch);
  if (ch == '(')
  {
    pushch_smt2(parser, '(');
    pushch_smt2(parser, 0);
    return BZLA_LPAR_TAG_SMT2;
  }
  if (ch == ')')
  {
    pushch_smt2(parser, ')');
    pushch_smt2(parser, 0);
    return BZLA_RPAR_TAG_SMT2;
  }
  if (ch == '#')
  {
    pushch_smt2(parser, '#');
    if ((ch = nextch_smt2(parser)) == EOF)
      return !perr_smt2(parser, "unexpected end-of-file after '#'");
    if (ch == 'b')
    {
      pushch_smt2(parser, 'b');
      if ((ch = nextch_smt2(parser)) == EOF)
        return !perr_smt2(parser, "unexpected end-of-file after '#b'");
      if (ch != '0' && ch != '1')
        return !perr_smt2(parser, "expected '0' or '1' after '#b'");
      pushch_smt2(parser, ch);
      for (;;)
      {
        ch = nextch_smt2(parser);
        if (ch != '0' && ch != '1') break;
        pushch_smt2(parser, ch);
      }
      savech_smt2(parser, ch);
      pushch_smt2(parser, 0);
      return BZLA_BINARY_CONSTANT_TAG_SMT2;
    }
    else if (ch == 'x')
    {
      pushch_smt2(parser, 'x');
      if ((ch = nextch_smt2(parser)) == EOF)
        return !perr_smt2(parser, "unexpected end-of-file after '#x'");
      if (!(cc_smt2(parser, ch) & BZLA_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2))
        return !perr_smt2(parser, "expected hexa-decimal digit after '#x'");
      pushch_smt2(parser, ch);
      for (;;)
      {
        ch = nextch_smt2(parser);
        if (!(cc_smt2(parser, ch) & BZLA_HEXADECIMAL_DIGIT_CHAR_CLASS_SMT2))
          break;
        pushch_smt2(parser, ch);
      }
      savech_smt2(parser, ch);
      pushch_smt2(parser, 0);
      return BZLA_HEXADECIMAL_CONSTANT_TAG_SMT2;
    }
    else
      return !perr_smt2(parser, "expected 'x' or 'b' after '#'");
  }
  else if (ch == '"')
  {
    pushch_smt2(parser, '"');
    for (;;)
    {
      if ((ch = nextch_smt2(parser)) == EOF)
      {
        return !cerr_smt2(parser, "unexpected", ch, "in string");
      }
      if (ch == '"')
      {
        pushch_smt2(parser, '"');
        ch = nextch_smt2(parser);
        if (ch != '"')
        {
          savech_smt2(parser, ch);
          pushch_smt2(parser, 0);
          return BZLA_STRING_CONSTANT_TAG_SMT2;
        }
      }
      if (!(cc_smt2(parser, ch) & BZLA_STRING_CHAR_CLASS_SMT2))
      {
        // TODO unreachable?
        return !cerr_smt2(parser, "invalid", ch, "in string");
      }
      pushch_smt2(parser, ch);
    }
  }
  else if (ch == '|')
  {
    pushch_smt2(parser, ch);
    for (;;)
    {
      if ((ch = nextch_smt2(parser)) == EOF)
        return !cerr_smt2(parser, "unexpected", ch, "in quoted symbol");
      pushch_smt2(parser, ch);
      if (ch == '|')
      {
        pushch_smt2(parser, 0);
        if (!(node = find_symbol_smt2(parser, parser->token.start)))
        {
          node       = new_node_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
          node->name = bzla_mem_strdup(parser->mem, parser->token.start);
          assert(!find_symbol_smt2(parser, node->name));
          insert_symbol_smt2(parser, node);
        }
        parser->last_node = node;
        return BZLA_SYMBOL_TAG_SMT2;
      }
    }
  }
  else if (ch == ':')
  {
    pushch_smt2(parser, ':');
    if ((ch = nextch_smt2(parser)) == EOF)
      return !perr_smt2(parser, "unexpected end-of-file after ':'");
    if (!(cc_smt2(parser, ch) & BZLA_KEYWORD_CHAR_CLASS_SMT2))
      return !cerr_smt2(parser, "unexpected", ch, "after ':'");
    pushch_smt2(parser, ch);
    while ((cc_smt2(parser, ch = nextch_smt2(parser))
            & BZLA_KEYWORD_CHAR_CLASS_SMT2))
    {
      assert(ch != EOF);
      pushch_smt2(parser, ch);
    }
    savech_smt2(parser, ch);
    pushch_smt2(parser, 0);
    if (!(node = find_symbol_smt2(parser, parser->token.start)))
    {
      node       = new_node_smt2(parser, BZLA_ATTRIBUTE_TAG_SMT2);
      node->name = bzla_mem_strdup(parser->mem, parser->token.start);
      assert(!find_symbol_smt2(parser, node->name));
      insert_symbol_smt2(parser, node);
    }
    parser->last_node = node;
    return node->tag;
  }
  else if (ch == '0')
  {
    res_tag = BZLA_DECIMAL_CONSTANT_TAG_SMT2;
    pushch_smt2(parser, '0');
    ch = nextch_smt2(parser);
    if (ch == '.')
    {
      res_tag = BZLA_REAL_CONSTANT_TAG_SMT2;
      pushch_smt2(parser, '.');
      if ((ch = nextch_smt2(parser)) == EOF)
        return !perr_smt2(parser, "unexpected end-of-file after '0.'");
      if (!(cc_smt2(parser, ch) & BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
        return !perr_smt2(parser, "expected decimal digit after '0.'");
      pushch_smt2(parser, ch);
      for (;;)
      {
        ch = nextch_smt2(parser);
        if (!(cc_smt2(parser, ch) & BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2)) break;
        pushch_smt2(parser, ch);
      }
    }
    savech_smt2(parser, ch);
    pushch_smt2(parser, 0);
    return res_tag;
  }
  else if (cc & BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2)
  {
    res_tag = BZLA_DECIMAL_CONSTANT_TAG_SMT2;
    pushch_smt2(parser, ch);
    for (;;)
    {
      ch = nextch_smt2(parser);
      if (!(cc_smt2(parser, ch) & BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2)) break;
      pushch_smt2(parser, ch);
    }
    if (ch == '.')
    {
      res_tag = BZLA_REAL_CONSTANT_TAG_SMT2;
      pushch_smt2(parser, '.');
      if ((ch = nextch_smt2(parser)) == EOF)
      {
        pushch_smt2(parser, 0);
        return !perr_smt2(
            parser, "unexpected end-of-file after '%s'", parser->token.start);
      }
      if (!(cc_smt2(parser, ch) & BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2))
      {
        pushch_smt2(parser, 0);
        return !perr_smt2(
            parser, "expected decimal digit after '%s'", parser->token.start);
      }
      pushch_smt2(parser, ch);
      for (;;)
      {
        ch = nextch_smt2(parser);
        if (!(cc_smt2(parser, ch) & BZLA_DECIMAL_DIGIT_CHAR_CLASS_SMT2)) break;
        pushch_smt2(parser, ch);
      }
    }
    savech_smt2(parser, ch);
    pushch_smt2(parser, 0);
    return res_tag;
  }
  else if (cc & BZLA_SYMBOL_CHAR_CLASS_SMT2)
  {
    pushch_smt2(parser, ch);
    for (;;)
    {
      ch = nextch_smt2(parser);
      if (!(cc_smt2(parser, ch) & BZLA_SYMBOL_CHAR_CLASS_SMT2)) break;
      pushch_smt2(parser, ch);
    }
    savech_smt2(parser, ch);
    pushch_smt2(parser, 0);
    if (!strcmp(parser->token.start, "_")) return BZLA_UNDERSCORE_TAG_SMT2;
    if (!(node = find_symbol_smt2(parser, parser->token.start)))
    {
      node       = new_node_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
      node->name = bzla_mem_strdup(parser->mem, parser->token.start);
      assert(!find_symbol_smt2(parser, node->name));
      insert_symbol_smt2(parser, node);
    }
    parser->last_node = node;
    return node->tag;
  }
  else
    return !cerr_smt2(parser, "illegal", ch, 0);

  return !perr_smt2(parser, "internal token reading error");
}

static int32_t
read_token_smt2(BzlaSMT2Parser *parser)
{
  int32_t res;
  parser->lastcoo = parser->coo;
  res             = read_token_aux_smt2(parser);
  if (bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_VERBOSITY) >= 4)
  {
    printf("[bzlasmt2] line %-8d column %-4d token %08x %s\n",
           parser->coo.x,
           parser->coo.y,
           res,
           res == EOF ? "<end-of-file>"
                      : res == BZLA_INVALID_TAG_SMT2 ? "<error>"
                                                     : parser->token.start);
    fflush(stdout);
  }
  return res;
}

static int32_t
read_rpar_smt2(BzlaSMT2Parser *parser, const char *msg)
{
  int32_t tag = read_token_smt2(parser);
  if (tag == EOF)
    return !perr_smt2(parser, "expected ')'%s at end-of-file", msg ? msg : "");
  if (tag == BZLA_INVALID_TAG_SMT2)
  {
    assert(parser->error);
    return 0;
  }
  if (tag != BZLA_RPAR_TAG_SMT2)
    return !perr_smt2(
        parser, "expected ')'%s at '%s'", msg ? msg : "", parser->token.start);
  return 1;
}

static int32_t
read_lpar_smt2(BzlaSMT2Parser *parser, const char *msg)
{
  int32_t tag = read_token_smt2(parser);
  if (tag == EOF)
    return !perr_smt2(parser, "expected '('%s at end-of-file", msg ? msg : "");
  if (tag == BZLA_INVALID_TAG_SMT2)
  {
    assert(parser->error);
    return 0;
  }
  if (tag != BZLA_LPAR_TAG_SMT2)
    return !perr_smt2(
        parser, "expected '('%s at '%s'", msg ? msg : "", parser->token.start);
  return 1;
}

static int32_t
skip_sexprs(BzlaSMT2Parser *parser, int32_t initial)
{
  int32_t tag, open = initial;
  while (open > 0)
  {
    tag = read_token_smt2(parser);
    if (tag == EOF)
    {
      if (open > 0) return !perr_smt2(parser, "')' missing at end-of-file");
      return 1;
    }
    if (tag == BZLA_INVALID_TAG_SMT2)
    {
      assert(parser->error);
      return 0;
    }
    else if (tag == BZLA_LPAR_TAG_SMT2)
      open++;
    else if (tag == BZLA_RPAR_TAG_SMT2)
      open--;
  }
  return 1;
}

static int32_t
read_symbol(BzlaSMT2Parser *parser, const char *errmsg, BzlaSMT2Node **resptr)
{
  int32_t tag = read_token_smt2(parser);
  if (tag == BZLA_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2(parser,
                      "expected symbol%s but reached end-of-file",
                      errmsg ? errmsg : "");
  if (tag != BZLA_SYMBOL_TAG_SMT2)
    return !perr_smt2(parser,
                      "expected symbol%s at '%s'",
                      errmsg ? errmsg : "",
                      parser->token.start);
  assert(parser->last_node->tag == BZLA_SYMBOL_TAG_SMT2);
  *resptr = parser->last_node;
  return 1;
}

static int32_t
str2uint32_smt2(BzlaSMT2Parser *parser,
                bool allow_zero,
                const char *str,
                uint32_t *resptr)
{
  uint64_t res;
  int32_t ch, digit;
  const char *p;
  res = 0;
  assert(sizeof(int32_t) == 4);
  for (p = str; (ch = *p); p++)
  {
    if (res > UINT32_MAX / 10 || ch < '0' || ch > '9')
    INVALID:
      return !perr_smt2(parser, "invalid 32-bit integer '%s'", str);
    assert('0' <= ch && ch <= '9');
    if (res) res *= 10;
    digit = ch - '0';
    if (UINT32_MAX - digit < res) goto INVALID;
    res += digit;
  }
  if (!allow_zero && !res)
    return !perr_smt2(
        parser, "expected positive non-zero 32-bit integer at '%s'", str);
  assert(res <= UINT32_MAX);
  *resptr = (uint32_t) res;
  return 1;
}

static BzlaSMT2Item *
push_item_smt2(BzlaSMT2Parser *parser, BzlaSMT2Tag tag)
{
  BzlaSMT2Item item;
  BZLA_CLR(&item);
  item.coo = parser->coo;
  item.tag = tag;
  BZLA_PUSH_STACK(parser->work, item);
  return parser->work.top - 1;
}

static BzlaSMT2Item *
last_lpar_smt2(BzlaSMT2Parser *parser)
{
  BzlaSMT2Item *p = parser->work.top;
  do
  {
    if (p-- == parser->work.start) return 0;
  } while (p->tag != BZLA_LPAR_TAG_SMT2);
  return p;
}

static bool
is_item_with_node_smt2(BzlaSMT2Item *item)
{
  if (item->tag == BZLA_SYMBOL_TAG_SMT2) return true;
  if (item->tag == BZLA_ATTRIBUTE_TAG_SMT2) return true;
  if (item->tag & BZLA_TAG_CLASS_MASK_SMT2) return true;
  return false;
}

static const char *
item2str_smt2(BzlaSMT2Item *item)
{
  if (is_item_with_node_smt2(item))
  {
    if (!item->node) return "<zero-node-item>";
    assert(item->node->name);
    return item->node->name;
  }
  else if (item->tag & BZLA_CONSTANT_TAG_CLASS_SMT2)
  {
    assert(item->str);
    return item->str;
  }
  else
    return "<non-printable-item>";
}

static bool
is_bvconst_str_smt2(const char *str)
{
  const char *p;
  if (str[0] != 'b' || str[1] != 'v') return false;
  if (!isdigit((int32_t) str[2])) return false;
  for (p = str + 3; *p; p++)
    if (!isdigit((int32_t) *p)) return false;
  return true;
}

static bool
prev_item_was_lpar_smt2(BzlaSMT2Parser *parser)
{
  if (BZLA_COUNT_STACK(parser->work) >= 2
      && parser->work.top[-2].tag == BZLA_LPAR_TAG_SMT2)
    return true;
  return !perr_smt2(parser, "expected '(' before '%s'", parser->token.start);
}

static bool
is_boolean_exp_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p)
{
  (void) parser;
  return !bitwuzla_term_is_array(p->exp) && !bitwuzla_term_is_fun(p->exp)
         && bitwuzla_term_bv_get_size(p->exp) == 1;
}

static int32_t
parse_uint32_smt2(BzlaSMT2Parser *parser, bool allow_zero, uint32_t *resptr)
{
  int32_t tag = read_token_smt2(parser);
  if (tag == BZLA_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2(parser,
                      "expected decimal constant but reached end-of-file");
  if (tag != BZLA_DECIMAL_CONSTANT_TAG_SMT2)
    return !perr_smt2(
        parser, "expected decimal constant at '%s'", parser->token.start);
  return str2uint32_smt2(parser, allow_zero, parser->token.start, resptr);
}

static bool
check_boolean_args_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p, int32_t nargs)
{
  int32_t i;
  uint32_t width;
  for (i = 1; i <= nargs; i++)
  {
    if (bitwuzla_term_is_array(p[i].exp))
    {
      parser->perrcoo = p[i].coo;
      return !perr_smt2(
          parser, "argument %d of '%s' is an array term", i, p->node->name);
    }
    if ((width = bitwuzla_term_bv_get_size(p[i].exp)) != 1)
    {
      parser->perrcoo = p[i].coo;
      return !perr_smt2(parser,
                        "argument %d of '%s' is a bit-vector of width %d",
                        i,
                        p->node->name,
                        width);
    }
  }
  return true;
}

static bool
check_arg_sorts_match_smt2(BzlaSMT2Parser *parser,
                           BzlaSMT2Item *p,
                           uint32_t offset,
                           uint32_t nargs)
{
  assert(nargs >= 1);

  uint32_t i, j;
  const BitwuzlaSort *sort;

  parser->perrcoo = p->coo;

  j    = offset + 1;
  sort = bitwuzla_term_get_sort(p[j].exp);

  for (i = j + 1; i <= nargs; ++i)
  {
    if (bitwuzla_term_get_sort(p[i].exp) == sort) continue;

    if (bitwuzla_term_is_array(p[j].exp) && !bitwuzla_term_is_array(p[i].exp))
    {
      return !perr_smt2(
          parser,
          "first argument of '%s' is an array but argument %d is not",
          p->node->name,
          i);
    }
    if (bitwuzla_term_is_fun(p[j].exp) && !bitwuzla_term_is_fun(p[i].exp))
    {
      return !perr_smt2(
          parser,
          "first argument of '%s' is a function but argument %d not",
          p->node->name,
          i);
    }
    return !perr_smt2(parser,
                      "sorts of arguments 1 and %d of '%s' do not match",
                      i,
                      p->node->name);
  }
  parser->perrcoo.x = 0;
  return true;
}

static bool
check_ite_args_sorts_match_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p)
{
  assert(p->tag == BZLA_ITE_TAG_SMT2);
  if (!bitwuzla_term_is_bv(p[1].exp)
      || bitwuzla_term_bv_get_size(p[1].exp) != 1)
  {
    parser->perrcoo = p[1].coo;
    return !perr_smt2(parser,
                      "first argument of 'ite' is not a bit-vector of size 1");
  }
  if (bitwuzla_term_get_sort(p[2].exp) != bitwuzla_term_get_sort(p[3].exp))
  {
    parser->perrcoo = p->coo;
    return !perr_smt2(
        parser, "sorts of second and third argument to 'ite' do not match");
  }
  return true;
}

static bool
check_nargs_smt2(BzlaSMT2Parser *parser,
                 BzlaSMT2Item *p,
                 int32_t actual,
                 int32_t required)
{
  int32_t diff   = actual - required;
  const char *op = p->node->name;
  if (diff) parser->perrcoo = p->coo;
  if (diff == -1) return !perr_smt2(parser, "one argument to '%s' missing", op);
  if (diff < 0)
    return !perr_smt2(parser, "%d arguments to '%s' missing", -diff, op);
  if (diff == 1)
    return !perr_smt2(parser, "'%s' has one argument too much", op);
  if (diff > 0)
    return !perr_smt2(parser, "'%s' has %d arguments too much", op, diff);
  return true;
}

static bool
check_bv_or_fp_args_smt2(BzlaSMT2Parser *parser,
                         BzlaSMT2Item *p,
                         uint32_t start,
                         uint32_t nargs,
                         bool check_fp)
{
  uint32_t i;
  (void) check_fp;
  char *is_str, *expected_str;
  bool is_err;

  for (i = start; i <= nargs; i++)
  {
    is_err = false;
    if (bitwuzla_term_is_array(p[i].exp))
    {
      is_str       = "an array";
      expected_str = "bit-vector";
      is_err       = true;
    }
    else if (bitwuzla_term_is_fun(p[i].exp))
    {
      is_str       = "a function";
      expected_str = "bit-vector";
      is_err       = true;
    }
    else if (bitwuzla_term_is_rm(p[i].exp))
    {
      is_str       = "a rounding mode term";
      expected_str = "bit-vector";
      is_err       = true;
    }
    else
    {
      if (check_fp && bitwuzla_term_is_bv(p[i].exp))
      {
        is_str       = "a bit-vector term";
        expected_str = "floating-point";
        is_err       = true;
      }
      else if (!check_fp && bitwuzla_term_is_fp(p[i].exp))
      {
        is_str       = "a floating-point term";
        expected_str = "bit-vector";
        is_err       = true;
      }
    }

    if (is_err)
    {
      parser->perrcoo = p[i].coo;
      return !perr_smt2(parser,
                        "argument %u of '%s' is %s, expected %s term",
                        i,
                        p->node->name,
                        is_str,
                        expected_str);
    }
  }
  return true;
}

static bool
check_bv_args_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p, uint32_t nargs)
{
  return check_bv_or_fp_args_smt2(parser, p, 1, nargs, false);
}

static bool
check_fp_args_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p, uint32_t nargs)
{
  return check_bv_or_fp_args_smt2(parser, p, 1, nargs, true);
}

static bool
check_rm_arg_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p, uint32_t idx)
{
  if (!bitwuzla_sort_is_rm(bitwuzla_term_get_sort(p[idx].exp)))
  {
    parser->perrcoo = p[idx].coo;
    return !perr_smt2(parser,
                      "argument %u of '%s' is not a rounding mode term",
                      idx,
                      p->node->name);
  }
  return true;
}

static bool
check_rm_fp_args_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p, uint32_t nargs)
{
  check_rm_arg_smt2(parser, p, 1);
  return check_bv_or_fp_args_smt2(parser, p, 2, nargs, true);
}

static bool
check_real_arg_smt2(BzlaSMT2Parser *parser, BzlaSMT2Item *p, uint32_t idx)
{
  if (p[idx].tag != BZLA_DECIMAL_CONSTANT_TAG_SMT2
      && p[idx].tag != BZLA_REAL_CONSTANT_TAG_SMT2)
  {
    parser->perrcoo = p[idx].coo;
    return !perr_smt2(parser,
                      "argument %u of '%s' is not a Real constant",
                      idx,
                      p->node->name);
  }
  return true;
}

static int32_t parse_sort(BzlaSMT2Parser *parser,
                          int32_t tag,
                          bool allow_array_sort,
                          const BitwuzlaSort **sort);

/* -------------------------------------------------------------------------- */

static void
release_exp_and_overwrite(BzlaSMT2Parser *parser,
                          BzlaSMT2Item *item_open,
                          BzlaSMT2Item *item_cur,
                          const BitwuzlaTerm *exp)
{
  parser->work.top = item_cur;
  item_open->tag   = BZLA_EXP_TAG_SMT2;
  item_open->exp   = exp;
}

static int32_t
parse_bit_width_smt2(BzlaSMT2Parser *parser, uint32_t *width)
{
  int32_t tag;

  tag = read_token_smt2(parser);
  if (tag == BZLA_INVALID_TAG_SMT2)
  {
    return 0;
  }
  if (tag == EOF)
  {
    return !perr_smt2(parser, "expected bit-width but reached end-of-file");
  }
  if (tag != BZLA_DECIMAL_CONSTANT_TAG_SMT2
      && tag != BZLA_REAL_CONSTANT_TAG_SMT2)
  {
    return !perr_smt2(
        parser, "expected bit-width at '%s'", parser->token.start);
  }
  assert(parser->token.start[0] != '-');
  if (strchr(parser->token.start, '.'))
  {
    return !perr_smt2(parser,
                      "invalid bit-width '%s', expected integer",
                      parser->token.start);
  }
  if (parser->token.start[0] == '0')
  {
    assert(!parser->token.start[1]);
    return !perr_smt2(parser, "invalid zero bit-width");
  }
  *width = 0;
  return str2uint32_smt2(parser, true, parser->token.start, width) ? 1 : 0;
}

/* -------------------------------------------------------------------------- */

/**
 * (OP Bool Bool Bool)
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_bin_bool(BzlaSMT2Parser *parser,
                    BzlaSMT2Item *item_open,
                    BzlaSMT2Item *item_cur,
                    uint32_t nargs,
                    BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_IMPLIES_TAG_SMT2
         || item_cur->tag == BZLA_AND_TAG_SMT2
         || item_cur->tag == BZLA_OR_TAG_SMT2
         || item_cur->tag == BZLA_XOR_TAG_SMT2);

  const BitwuzlaTerm *exp;

  if (nargs < 2)
  {
    parser->perrcoo = item_cur->coo;
    return !perr_smt2(parser, "argument to '%s' missing", item_cur->node->name);
  }

  if (!check_boolean_args_smt2(parser, item_cur, nargs)) return 0;

  BitwuzlaTermConstPtrStack args;
  BZLA_INIT_STACK(parser->mem, args);
  for (uint32_t i = 1; i <= nargs; i++) BZLA_PUSH_STACK(args, item_cur[i].exp);
  exp = bitwuzla_mk_term(parser->bitwuzla, kind, nargs, args.start);
  BZLA_RELEASE_STACK(args);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);

  return 1;
}

/**
 * (OP (_ BitVec m) (_ BitVec m))
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_unary_bv_fun(BzlaSMT2Parser *parser,
                        BzlaSMT2Item *item_open,
                        BzlaSMT2Item *item_cur,
                        uint32_t nargs,
                        BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_BV_NOT_TAG_SMT2
         || item_cur->tag == BZLA_BV_NEG_TAG_SMT2
         || item_cur->tag == BZLA_BV_REDOR_TAG_SMT2
         || item_cur->tag == BZLA_BV_REDXOR_TAG_SMT2
         || item_cur->tag == BZLA_BV_REDAND_TAG_SMT2);

  const BitwuzlaTerm *exp;

  if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
  if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
  exp = bitwuzla_mk_term1(parser->bitwuzla, kind, item_cur[1].exp);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * (LEFT_ASSOCIATIVE_OP (_ BitVec m) (_ BitVec m) (_ BitVec m))
 * (concat (_ BitVec m) (_ BitVec n) (_ BitVec m+n))
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_bin_bv_left_associative(BzlaSMT2Parser *parser,
                                   BzlaSMT2Item *item_open,
                                   BzlaSMT2Item *item_cur,
                                   uint32_t nargs,
                                   BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_BV_CONCAT_TAG_SMT2
         || item_cur->tag == BZLA_BV_AND_TAG_SMT2
         || item_cur->tag == BZLA_BV_OR_TAG_SMT2
         || item_cur->tag == BZLA_BV_XOR_TAG_SMT2
         || item_cur->tag == BZLA_BV_ADD_TAG_SMT2
         || item_cur->tag == BZLA_BV_SUB_TAG_SMT2
         || item_cur->tag == BZLA_BV_MUL_TAG_SMT2);

  if (nargs < 2)
  {
    parser->perrcoo = item_cur->coo;
    return !perr_smt2(parser, "argument to '%s' missing", item_cur->node->name);
  }

  if (item_cur->tag != BZLA_BV_CONCAT_TAG_SMT2
      && !check_arg_sorts_match_smt2(parser, item_cur, 0, nargs))
  {
    return 0;
  }

  if (!check_bv_args_smt2(parser, item_cur, nargs))
  {
    return 0;
  }

  BitwuzlaTermConstPtrStack args;
  BZLA_INIT_STACK(parser->mem, args);
  for (uint32_t i = 1; i <= nargs; i++) BZLA_PUSH_STACK(args, item_cur[i].exp);
  const BitwuzlaTerm *exp =
      bitwuzla_mk_term(parser->bitwuzla, kind, nargs, args.start);
  BZLA_RELEASE_STACK(args);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);

  return 1;
}

/**
 * (OP (_ BitVec m) (_ BitVec m) (_ BitVec m))
 * (OP (_ BitVec m) (_ BitVec m) Bool)
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_bin_bv_fun(BzlaSMT2Parser *parser,
                      BzlaSMT2Item *item_open,
                      BzlaSMT2Item *item_cur,
                      uint32_t nargs,
                      BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_BV_UDIV_TAG_SMT2
         || item_cur->tag == BZLA_BV_UREM_TAG_SMT2
         || item_cur->tag == BZLA_BV_SHL_TAG_SMT2
         || item_cur->tag == BZLA_BV_LSHR_TAG_SMT2
         || item_cur->tag == BZLA_BV_ASHR_TAG_SMT2
         || item_cur->tag == BZLA_BV_NAND_TAG_SMT2
         || item_cur->tag == BZLA_BV_NOR_TAG_SMT2
         || item_cur->tag == BZLA_BV_XNOR_TAG_SMT2
         || item_cur->tag == BZLA_BV_COMP_TAG_SMT2
         || item_cur->tag == BZLA_BV_SDIV_TAG_SMT2
         || item_cur->tag == BZLA_BV_SREM_TAG_SMT2
         || item_cur->tag == BZLA_BV_SMOD_TAG_SMT2
         || item_cur->tag == BZLA_BV_ULT_TAG_SMT2
         || item_cur->tag == BZLA_BV_ULE_TAG_SMT2
         || item_cur->tag == BZLA_BV_UGT_TAG_SMT2
         || item_cur->tag == BZLA_BV_UGE_TAG_SMT2
         || item_cur->tag == BZLA_BV_SLT_TAG_SMT2
         || item_cur->tag == BZLA_BV_SLE_TAG_SMT2
         || item_cur->tag == BZLA_BV_SGT_TAG_SMT2
         || item_cur->tag == BZLA_BV_SGE_TAG_SMT2
         || item_cur->tag == BZLA_BV_SADDO_TAG_SMT2
         || item_cur->tag == BZLA_BV_UADDO_TAG_SMT2
         || item_cur->tag == BZLA_BV_SDIVO_TAG_SMT2
         || item_cur->tag == BZLA_BV_SMULO_TAG_SMT2
         || item_cur->tag == BZLA_BV_UMULO_TAG_SMT2
         || item_cur->tag == BZLA_BV_SSUBO_TAG_SMT2
         || item_cur->tag == BZLA_BV_USUBO_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 2)) return 0;
  if (!check_arg_sorts_match_smt2(parser, item_cur, 0, 2)) return 0;
  if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
  const BitwuzlaTerm *exp = bitwuzla_mk_term2(
      parser->bitwuzla, kind, item_cur[1].exp, item_cur[2].exp);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))
 * ((_ sign_extend i) (_ BitVec m) (_ BitVec m+i))
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_extend_bv_fun(BzlaSMT2Parser *parser,
                         BzlaSMT2Item *item_open,
                         BzlaSMT2Item *item_cur,
                         uint32_t nargs,
                         BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_BV_ZERO_EXTEND_TAG_SMT2
         || item_cur->tag == BZLA_BV_SIGN_EXTEND_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
  if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
  uint32_t width = bitwuzla_term_bv_get_size(item_cur[1].exp);
  if ((uint32_t)(INT32_MAX - item_cur->num) < width)
  {
    parser->perrcoo = item_cur->coo;
    return !perr_smt2(
        parser, "resulting bit-width of '%s' too large", item_cur->node->name);
  }
  const BitwuzlaTerm *exp = bitwuzla_mk_term1_indexed1(
      parser->bitwuzla, kind, item_cur[1].exp, item_cur->num);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * ((_ rotate_left i) (_ BitVec m) (_ BitVec m))
 * ((_ rotate_right i) (_ BitVec m) (_ BitVec m))
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_rotate_bv_fun(BzlaSMT2Parser *parser,
                         BzlaSMT2Item *item_open,
                         BzlaSMT2Item *item_cur,
                         uint32_t nargs,
                         BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_BV_ROTATE_LEFT_TAG_SMT2
         || item_cur->tag == BZLA_BV_ROTATE_RIGHT_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
  if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
  uint32_t width          = bitwuzla_term_bv_get_size(item_cur[1].exp);
  const BitwuzlaTerm *exp = bitwuzla_mk_term1_indexed1(
      parser->bitwuzla, kind, item_cur[1].exp, item_cur->num % width);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * (
 *   OP (_ FloatingPoint eb sb)
 *   (_ FloatingPoint eb sb)
 * )
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_unary_fp_fun(BzlaSMT2Parser *parser,
                        BzlaSMT2Item *item_open,
                        BzlaSMT2Item *item_cur,
                        uint32_t nargs,
                        BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_FP_ABS_TAG_SMT2
         || item_cur->tag == BZLA_FP_NEG_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
  if (!check_fp_args_smt2(parser, item_cur, nargs)) return 0;
  const BitwuzlaTerm *exp =
      bitwuzla_mk_term1(parser->bitwuzla, kind, item_cur[1].exp);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * (
 *   OP RoundingMode (_ FloatingPoint eb sb)
 *   (_ FloatingPoint eb sb)
 * )
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_unary_rm_fp_fun(BzlaSMT2Parser *parser,
                           BzlaSMT2Item *item_open,
                           BzlaSMT2Item *item_cur,
                           uint32_t nargs,
                           BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_FP_ROUND_TO_INT_TAG_SMT2
         || item_cur->tag == BZLA_FP_SQRT_TAG_SMT2
         || item_cur->tag == BZLA_FP_TO_SBV_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 2)) return 0;
  if (!check_rm_fp_args_smt2(parser, item_cur, nargs)) return 0;
  const BitwuzlaTerm *exp = bitwuzla_mk_term2(
      parser->bitwuzla, kind, item_cur[1].exp, item_cur[2].exp);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * (
 *   OP (_ FloatingPoint eb sb)
 *   Bool
 * )
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_unary_bool_fp_fun(BzlaSMT2Parser *parser,
                             BzlaSMT2Item *item_open,
                             BzlaSMT2Item *item_cur,
                             uint32_t nargs,
                             BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_FP_IS_NORMAL_TAG_SMT2
         || item_cur->tag == BZLA_FP_IS_SUBNORMAL_TAG_SMT2
         || item_cur->tag == BZLA_FP_IS_ZERO_TAG_SMT2
         || item_cur->tag == BZLA_FP_IS_INF_TAG_SMT2
         || item_cur->tag == BZLA_FP_IS_NAN_TAG_SMT2
         || item_cur->tag == BZLA_FP_IS_NEG_TAG_SMT2
         || item_cur->tag == BZLA_FP_IS_POS_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
  if (!check_fp_args_smt2(parser, item_cur, nargs)) return 0;
  const BitwuzlaTerm *exp =
      bitwuzla_mk_term1(parser->bitwuzla, kind, item_cur[1].exp);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * (
 *   OP (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
 *   (_ FloatingPoint eb sb)
 * )
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_bin_fp_fun(BzlaSMT2Parser *parser,
                      BzlaSMT2Item *item_open,
                      BzlaSMT2Item *item_cur,
                      uint32_t nargs,
                      BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_FP_REM_TAG_SMT2
         || item_cur->tag == BZLA_FP_MIN_TAG_SMT2
         || item_cur->tag == BZLA_FP_MAX_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 2)) return 0;
  if (!check_fp_args_smt2(parser, item_cur, nargs)) return 0;
  if (!check_arg_sorts_match_smt2(parser, item_cur, 0, 2)) return 0;
  const BitwuzlaTerm *exp = bitwuzla_mk_term2(
      parser->bitwuzla, kind, item_cur[1].exp, item_cur[2].exp);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * (
 *   OP (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
 *   Bool
 * )
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_bin_fp_fun_chainable(BzlaSMT2Parser *parser,
                                BzlaSMT2Item *item_open,
                                BzlaSMT2Item *item_cur,
                                uint32_t nargs,
                                BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_FP_EQ_TAG_SMT2
         || item_cur->tag == BZLA_FP_LEQ_TAG_SMT2
         || item_cur->tag == BZLA_FP_LT_TAG_SMT2
         || item_cur->tag == BZLA_FP_GEQ_TAG_SMT2
         || item_cur->tag == BZLA_FP_GT_TAG_SMT2);

  BitwuzlaTermConstPtrStack args;
  Bitwuzla *bitwuzla = parser->bitwuzla;

  BZLA_INIT_STACK(parser->mem, args);
  if (!check_fp_args_smt2(parser, item_cur, nargs)) return 0;
  if (!check_arg_sorts_match_smt2(parser, item_cur, 0, nargs)) return 0;
  for (uint32_t i = 1; i <= nargs; i++) BZLA_PUSH_STACK(args, item_cur[i].exp);
  const BitwuzlaTerm *exp = bitwuzla_mk_term(bitwuzla, kind, nargs, args.start);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  BZLA_RELEASE_STACK(args);
  return 1;
}

/**
 * (
 *   OP RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
 *   (_ FloatingPoint eb sb)
 * )
 *
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_bin_rm_fp_fun(BzlaSMT2Parser *parser,
                         BzlaSMT2Item *item_open,
                         BzlaSMT2Item *item_cur,
                         uint32_t nargs,
                         BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_FP_ADD_TAG_SMT2
         || item_cur->tag == BZLA_FP_SUB_TAG_SMT2
         || item_cur->tag == BZLA_FP_MUL_TAG_SMT2
         || item_cur->tag == BZLA_FP_DIV_TAG_SMT2);

  if (!check_nargs_smt2(parser, item_cur, nargs, 3)) return 0;
  if (!check_rm_fp_args_smt2(parser, item_cur, nargs)) return 0;
  if (!check_arg_sorts_match_smt2(parser, item_cur, 1, 2)) return 0;
  const BitwuzlaTerm *exp = bitwuzla_mk_term3(parser->bitwuzla,
                                              kind,
                                              item_cur[1].exp,
                                              item_cur[2].exp,
                                              item_cur[3].exp);
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * (
 *   (_ to_fp eb sb) RoundingMode (_ FloatingPoint eb sb)
 *   (_ FloatingPoint eb sb)
 * )
 * (
 *   (_ to_fp eb sb) RoundingMode (_ BitVec m)
 *   (_ FloatingPoint eb sb)
 * )
 * (
 *   (_ to_fp eb sb) RoundingMode Real
 *   (_ FloatingPoint eb sb)
 * )
 * (
 *   (_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m)
 *   (_ FloatingPoint eb sb)
 * )
 * Note: item_open and item_cur point to items on the parser work stack.
 *       If if nargs > 0, we expect nargs SMT2Items on the stack after
 *       item_cur: item_cur[1] is the first argument, ..., item_cur[nargs] is
 *       the last argument.
 */
static int32_t
close_term_to_fp_two_args(BzlaSMT2Parser *parser,
                          BzlaSMT2Item *item_open,
                          BzlaSMT2Item *item_cur,
                          uint32_t nargs)
{
  assert(parser);
  assert(item_open);
  assert(item_cur->idx0);
  assert(item_cur->idx1);
  assert(item_cur);

  const BitwuzlaTerm *exp;
  Bitwuzla *bitwuzla = parser->bitwuzla;

  if (!check_nargs_smt2(parser, item_cur, nargs, 2)) return 0;
  if (!check_rm_arg_smt2(parser, item_cur, 1)) return 0;
  if (item_cur[2].tag != BZLA_EXP_TAG_SMT2
      && item_cur[2].tag != BZLA_REAL_CONSTANT_TAG_SMT2
      && item_cur[2].tag != BZLA_REAL_DIV_TAG_SMT2)
  {
    parser->perrcoo = item_cur[2].coo;
    return !perr_smt2(parser, "expected expression or real constant");
  }

  if (item_cur[2].tag == BZLA_REAL_CONSTANT_TAG_SMT2)
  {
    const BitwuzlaSort *s =
        bitwuzla_mk_fp_sort(bitwuzla, item_cur->idx0, item_cur->idx1);
    exp = bitwuzla_mk_fp_value_from_real(
        bitwuzla, s, item_cur[1].exp, item_cur[2].str);
    bzla_mem_freestr(parser->mem, item_cur[2].str);
  }
  else if (item_cur[2].tag == BZLA_REAL_DIV_TAG_SMT2)
  {
    const BitwuzlaSort *s =
        bitwuzla_mk_fp_sort(bitwuzla, item_cur->idx0, item_cur->idx1);
    exp = bitwuzla_mk_fp_value_from_rational(
        bitwuzla, s, item_cur[1].exp, item_cur[2].strs[0], item_cur[2].strs[1]);
    bzla_mem_freestr(parser->mem, item_cur[2].strs[0]);
    bzla_mem_freestr(parser->mem, item_cur[2].strs[1]);
  }
  else
  {
    const BitwuzlaSort *s      = bitwuzla_term_get_sort(item_cur[2].exp);
    const BitwuzlaTerm *args[] = {item_cur[1].exp, item_cur[2].exp};
    uint32_t idxs[]      = {item_cur->idx0, item_cur->idx1};
    if (item_cur->tag == BZLA_FP_TO_FP_UNSIGNED_TAG_SMT2)
    {
      /* (_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) */
      if (!bitwuzla_sort_is_bv(s))
      {
        return !perr_smt2(parser,
                          "invalid argument to '%s', expected bit-vector term",
                          item_cur->node->name);
      }
      exp = bitwuzla_mk_term_indexed(
          bitwuzla, BITWUZLA_KIND_FP_TO_FP_FROM_UBV, 2, args, 2, idxs);
    }
    else
    {
      assert(item_cur->tag == BZLA_FP_TO_FP_TAG_SMT2);
      if (bitwuzla_sort_is_bv(s))
      {
        /* (_ to_fp eb sb) RoundingMode (_ BitVec m) */
        exp = bitwuzla_mk_term_indexed(
            bitwuzla, BITWUZLA_KIND_FP_TO_FP_FROM_SBV, 2, args, 2, idxs);
      }
      else if (bitwuzla_sort_is_fp(s))
      {
        /* (_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) */
        exp = bitwuzla_mk_term_indexed(
            bitwuzla, BITWUZLA_KIND_FP_TO_FP_FROM_FP, 2, args, 2, idxs);
      }
      else
      {
        return !perr_smt2(
            parser,
            "invalid argument to '%s', expected bit-vector or floating-point "
            "term",
            item_cur->node->name);
      }
    }
  }
  release_exp_and_overwrite(parser, item_open, item_cur, exp);
  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term_quant(BzlaSMT2Parser *parser,
                 BzlaSMT2Item *item_open,
                 BzlaSMT2Item *item_cur,
                 uint32_t nargs,
                 BitwuzlaKind kind)
{
  assert(parser);
  assert(item_open);
  assert(item_cur);

  assert(item_cur->tag == BZLA_FORALL_TAG_SMT2
         || item_cur->tag == BZLA_EXISTS_TAG_SMT2);

  BitwuzlaTermConstPtrStack args;
  uint32_t i;
  char *msg;
  BzlaSMT2Node *sym;

  msg = item_cur->tag == BZLA_FORALL_TAG_SMT2 ? "forall" : "exists";

  for (i = 1; i < nargs; i++)
  {
    if (item_cur[i].tag != BZLA_SYMBOL_TAG_SMT2)
    {
      parser->perrcoo = item_cur[i].coo;
      return !perr_smt2(
          parser, "expected symbol as argument %d of '%s'", i, msg);
    }
  }
  if (item_cur[nargs].tag != BZLA_SYMBOL_TAG_SMT2
      && item_cur[nargs].tag != BZLA_EXP_TAG_SMT2)
  {
    parser->perrcoo = item_cur[nargs].coo;
    return !perr_smt2(
        parser, "expected expression as argument %d of '%s'", nargs, msg);
  }
  if (!is_boolean_exp_smt2(parser, item_cur + nargs))
  {
    parser->perrcoo = item_cur[nargs].coo;
    return !perr_smt2(parser, "body of '%s' is not a boolean term", msg);
  }
  BZLA_INIT_STACK(parser->mem, args);
  for (i = 1; i < nargs; i++)
  {
    assert(item_cur[i].tag == BZLA_SYMBOL_TAG_SMT2);
    sym = item_cur[i].node;
    assert(sym);
    assert(sym->coo.x);
    assert(sym->tag);
    assert(sym->tag == BZLA_SYMBOL_TAG_SMT2);
    assert(sym->exp);
    BZLA_PUSH_STACK(args, sym->exp);
    remove_symbol_smt2(parser, sym);
  }
  BZLA_PUSH_STACK(args, item_cur[nargs].exp);
  item_open[0].tag = BZLA_EXP_TAG_SMT2;
  item_open[0].exp = bitwuzla_mk_term(
      parser->bitwuzla, kind, BZLA_COUNT_STACK(args), args.start);
  BZLA_RELEASE_STACK(args);
  parser->work.top = item_cur;
  return 1;
}

/**
 * item_open and item_cur point to items on the parser work stack.
 * If if nargs > 0, we expect nargs SMT2Items on the stack after item_cur:
 * item_cur[1] is the first argument, ..., item_cur[nargs] is the last argument.
 */
static int32_t
close_term(BzlaSMT2Parser *parser)
{
  assert(parser);

  const BitwuzlaTerm *exp, *tmp;
  int32_t open, tag;
  uint32_t i, width, nargs;
  BzlaSMT2Item *item_open;
  BzlaSMT2Item *item_cur;
  BzlaSMT2Node *sym;
  Bitwuzla *bitwuzla = parser->bitwuzla;

  open = parser->open;

  if (parser->expecting_body)
  {
    item_open = 0;
    if (open)
    {
      item_open = last_lpar_smt2(parser);
      if (++item_open >= parser->work.top) item_open = 0;
    }
    if (item_open)
    {
      assert(item_open->tag == BZLA_LET_TAG_SMT2);
      return !perr_smt2(parser,
                        "body to '%s' at line %d column %d missing",
                        parser->expecting_body,
                        item_open->coo.x,
                        item_open->coo.y);
    }
    else
    {
      return !perr_smt2(parser, "body to 'let' missing");
    }
  }
  assert(open >= 0);
  if (!open) return !perr_smt2(parser, "expected expression");
  item_open = last_lpar_smt2(parser);
  assert(item_open);
  item_cur = item_open + 1;
  if (item_cur == parser->work.top)
    return !perr_smt2(parser, "unexpected '()'");
  nargs = parser->work.top - item_cur - 1;
  tag   = item_cur->tag;

  /* check if operands are expressions -------------------------------------- */
  if (tag != BZLA_LET_TAG_SMT2 && tag != BZLA_LETBIND_TAG_SMT2
      && tag != BZLA_PARLETBINDING_TAG_SMT2 && tag != BZLA_REAL_DIV_TAG_SMT2
      && tag != BZLA_SORTED_VAR_TAG_SMT2 && tag != BZLA_SORTED_VARS_TAG_SMT2
      && tag != BZLA_FORALL_TAG_SMT2 && tag != BZLA_EXISTS_TAG_SMT2
      && tag != BZLA_BANG_TAG_SMT2)
  {
    i = 1;
    for (; i <= nargs; i++)
    {
      if (item_cur[i].tag != BZLA_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        if (item_cur[i].tag == BZLA_REAL_CONSTANT_TAG_SMT2
            || item_cur[i].tag == BZLA_REAL_DIV_TAG_SMT2)
        {
          if (tag == BZLA_FP_TO_FP_TAG_SMT2) continue;
          return !perr_smt2(parser, "Real constants not supported");
        }
        return !perr_smt2(parser, "expected expression");
      }
    }
  }

  /* expression ------------------------------------------------------------- */
  if (tag == BZLA_EXP_TAG_SMT2)
  {
    /* function application */
    if (nargs && bitwuzla_term_is_fun(item_cur[0].exp))
    {
      BitwuzlaTermConstPtrStack fargs;
      BZLA_INIT_STACK(parser->mem, fargs);

      const BitwuzlaTerm *fun = item_cur[0].exp;
      if (nargs != bitwuzla_term_fun_get_arity(fun))
      {
        BZLA_RELEASE_STACK(fargs);
        return !perr_smt2(parser, "invalid number of arguments");
      }

      size_t size;
      const BitwuzlaSort **domain_sorts =
          bitwuzla_term_fun_get_domain_sorts(fun, &size);

      BZLA_PUSH_STACK(fargs, fun);
      for (i = 1; i <= nargs; i++)
      {
        if (item_cur[i].tag != BZLA_EXP_TAG_SMT2)
        {
          BZLA_RELEASE_STACK(fargs);
          parser->perrcoo = item_cur[i].coo;
          return !perr_smt2(parser, "expected expression");
        }
        BZLA_PUSH_STACK(fargs, item_cur[i].exp);
        assert(i - 1 < size);
        assert(domain_sorts[i - 1]);
        if (!bitwuzla_sort_is_equal(
                domain_sorts[i - 1],
                bitwuzla_term_get_sort(BZLA_PEEK_STACK(fargs, i))))
        {
          BZLA_RELEASE_STACK(fargs);
          return !perr_smt2(parser, "invalid sort for argument %d", i);
        }
      }
      parser->work.top = item_cur;
      item_open->tag   = BZLA_EXP_TAG_SMT2;
      item_open->exp   = bitwuzla_mk_term(
          bitwuzla, BITWUZLA_KIND_APPLY, BZLA_COUNT_STACK(fargs), fargs.start);
      BZLA_RELEASE_STACK(fargs);
    }
    else
    {
      if (nargs)
      {
        parser->perrcoo = item_open->coo;
        return !perr_smt2(parser, "list with %d expressions", nargs + 1);
      }
      item_cur->coo = item_open->coo;
      *item_open    = *item_cur;
      parser->work.top--;
      assert(item_open + 1 == parser->work.top);
    }
  }
  else if (tag == BZLA_AS_TAG_SMT2)
  {
    if (nargs != 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser,
          "expected exactly one argument for ((as ...) but got %u",
          nargs);
    }
    exp = bitwuzla_mk_const_array(bitwuzla, item_cur->sort, item_cur[1].exp);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  else if (tag == BZLA_BANG_TAG_SMT2)
  {
    if (nargs != 3)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser,
          "invalid annotation syntax, expected 3 arguments got %u",
          nargs);
    }
    if (item_cur[1].tag != BZLA_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(
          parser,
          "invalid annotation syntax, expected expression as first argument");
    }
    if (item_cur[2].tag != BZLA_NAMED_TAG_SMT2)
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser,
                        "invalid annotation syntax, expected :named attribute "
                        "as second argument");
    }
    if (item_cur[3].tag != BZLA_SYMBOL_TAG_SMT2)
    {
      parser->perrcoo = item_cur[3].coo;
      return !perr_smt2(
          parser,
          "invalid annotation syntax, expected symbol as third argument");
    }
    tmp = item_cur[1].exp;
    bitwuzla_term_set_symbol(tmp, item_cur[3].node->name);
    parser->work.top = item_cur;
    item_open->tag   = BZLA_EXP_TAG_SMT2;
    item_open->exp   = tmp;
  }
  /* CORE: NOT -------------------------------------------------------------- */
  else if (tag == BZLA_NOT_TAG_SMT2)
  {
    if (nargs != 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser, "'not' with %d arguments but expected exactly one", nargs);
    }
    tmp = item_cur[1].exp;
    if (!bitwuzla_term_is_bv(tmp) || bitwuzla_term_bv_get_size(tmp) != 1)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser, "expected bit-vector of size 1");
    }
    parser->work.top = item_cur;
    item_open->tag   = BZLA_EXP_TAG_SMT2;
    item_open->exp   = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_NOT, tmp);
  }
  /* CORE: IMPLIES ---------------------------------------------------------- */
  else if (tag == BZLA_IMPLIES_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_IMPLIES))
    {
      return 0;
    }
  }
  /* CORE: AND -------------------------------------------------------------- */
  else if (tag == BZLA_AND_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_AND))
    {
      return 0;
    }
  }
  /* CORE: OR --------------------------------------------------------------- */
  else if (tag == BZLA_OR_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_OR))
    {
      return 0;
    }
  }
  /* CORE: XOR -------------------------------------------------------------- */
  else if (tag == BZLA_XOR_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_XOR))
    {
      return 0;
    }
  }
  /* CORE: EQUAL ------------------------------------------------------------ */
  else if (tag == BZLA_EQUAL_TAG_SMT2)
  {
    if (!nargs)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "arguments to '=' missing");
    }
    if (nargs == 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "only one argument to '='");
    }
    if (!check_arg_sorts_match_smt2(parser, item_cur, 0, nargs)) return 0;
    BitwuzlaTermConstPtrStack args;
    BZLA_INIT_STACK(parser->mem, args);
    for (uint32_t i = 1; i <= nargs; i++)
      BZLA_PUSH_STACK(args, item_cur[i].exp);
    exp = bitwuzla_mk_term(bitwuzla, BITWUZLA_KIND_EQUAL, nargs, args.start);
    BZLA_RELEASE_STACK(args);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* CORE: DISTINCT --------------------------------------------------------- */
  else if (tag == BZLA_DISTINCT_TAG_SMT2)
  {
    if (!nargs)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "arguments to 'distinct' missing");
    }
    if (nargs == 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "only one argument to 'distinct'");
    }
    if (!check_arg_sorts_match_smt2(parser, item_cur, 0, nargs)) return 0;
    BitwuzlaTermConstPtrStack args;
    BZLA_INIT_STACK(parser->mem, args);
    for (uint32_t i = 1; i <= nargs; i++)
      BZLA_PUSH_STACK(args, item_cur[i].exp);
    exp = bitwuzla_mk_term(bitwuzla, BITWUZLA_KIND_DISTINCT, nargs, args.start);
    BZLA_RELEASE_STACK(args);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* CORE: ITE -------------------------------------------------------------- */
  else if (tag == BZLA_ITE_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 3)) return 0;
    if (!check_ite_args_sorts_match_smt2(parser, item_cur)) return 0;
    exp = bitwuzla_mk_term3(bitwuzla,
                            BITWUZLA_KIND_ITE,
                            item_cur[1].exp,
                            item_cur[2].exp,
                            item_cur[3].exp);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* ARRAY: SELECT ---------------------------------------------------------- */
  else if (tag == BZLA_ARRAY_SELECT_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 2)) return 0;
    if (!bitwuzla_term_is_array(item_cur[1].exp))
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser, "first argument of 'select' is not an array");
    }
    if (bitwuzla_term_is_array(item_cur[2].exp))
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "second argument of 'select' is an array");
    }
    if (bitwuzla_term_is_fun(item_cur[2].exp))
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "second argument of 'select' is a function");
    }
    if (bitwuzla_term_get_sort(item_cur[2].exp)
        != bitwuzla_term_array_get_index_sort(item_cur[1].exp))
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser,
          "index sort of array (first) argument and sort of index "
          "(second) argument to 'select' do not match");
    }
    exp = bitwuzla_mk_term2(
        bitwuzla, BITWUZLA_KIND_ARRAY_SELECT, item_cur[1].exp, item_cur[2].exp);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* ARRAY: STORE ----------------------------------------------------------- */
  else if (tag == BZLA_ARRAY_STORE_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 3)) return 0;
    if (!bitwuzla_term_is_array(item_cur[1].exp))
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser, "first argument of 'store' is not an array");
    }
    if (bitwuzla_term_is_array(item_cur[2].exp))
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "second argument of 'store' is an array");
    }
    if (bitwuzla_term_is_fun(item_cur[2].exp))
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "second argument of 'store' is a function");
    }
    if (bitwuzla_term_is_array(item_cur[3].exp))
    {
      parser->perrcoo = item_cur[3].coo;
      return !perr_smt2(parser, "third argument of 'store' is an array");
    }
    if (bitwuzla_term_get_sort(item_cur[2].exp)
        != bitwuzla_term_array_get_index_sort(item_cur[1].exp))
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser,
          "index sort of array (first) argument and sort of index "
          "(second) argument to 'store' do not match");
    }
    if (bitwuzla_term_get_sort(item_cur[3].exp)
        != bitwuzla_term_array_get_element_sort(item_cur[1].exp))
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser,
          "element sort of array (first) argument and sort of element "
          "(second) argument to 'store' do not match");
    }
    exp = bitwuzla_mk_term3(bitwuzla,
                            BITWUZLA_KIND_ARRAY_STORE,
                            item_cur[1].exp,
                            item_cur[2].exp,
                            item_cur[3].exp);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* BV: EXTRACT ------------------------------------------------------------ */
  else if (tag == BZLA_BV_EXTRACT_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
    if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
    width = bitwuzla_term_bv_get_size(item_cur[1].exp);
    if (width <= (uint32_t) item_cur->idx0)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser,
                        "first (high) 'extract' parameter %u too large "
                        "for bit-vector argument of bit-width %u",
                        item_cur->idx0,
                        width);
    }
    exp = bitwuzla_mk_term1_indexed2(bitwuzla,
                                     BITWUZLA_KIND_BV_EXTRACT,
                                     item_cur[1].exp,
                                     item_cur->idx0,
                                     item_cur->idx1);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* BV: NOT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_NOT_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NOT))
    {
      return 0;
    }
  }
  /* BV: NEG ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_NEG_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NEG))
    {
      return 0;
    }
  }
  /* BV: REDOR -------------------------------------------------------------- */
  else if (tag == BZLA_BV_REDOR_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_REDOR))
    {
      return 0;
    }
  }
  /* BV: REDXOR ------------------------------------------------------------- */
  else if (tag == BZLA_BV_REDXOR_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_REDXOR))
    {
      return 0;
    }
  }
  /* BV: REDAND ------------------------------------------------------------- */
  else if (tag == BZLA_BV_REDAND_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_REDAND))
    {
      return 0;
    }
  }
  /* BV: CONCAT ------------------------------------------------------------- */
  else if (tag == BZLA_BV_CONCAT_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_CONCAT))
    {
      return 0;
    }
  }
  /* BV: AND ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_AND_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_AND))
    {
      return 0;
    }
  }
  /* BV: OR ----------------------------------------------------------------- */
  else if (tag == BZLA_BV_OR_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_OR))
    {
      return 0;
    }
  }
  /* BV: XOR ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_XOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_XOR))
    {
      return 0;
    }
  }
  /* BV: ADD ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_ADD_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ADD))
    {
      return 0;
    }
  }
  /* BV: SUB ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SUB_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SUB))
    {
      return 0;
    }
  }
  /* BV: MUL ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_MUL_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_MUL))
    {
      return 0;
    }
  }
  /* BV: UDIV --------------------------------------------------------------- */
  else if (tag == BZLA_BV_UDIV_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UDIV))
    {
      return 0;
    }
  }
  /* BV: UREM --------------------------------------------------------------- */
  else if (tag == BZLA_BV_UREM_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UREM))
    {
      return 0;
    }
  }
  /* BV: SHL ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SHL_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SHL))
    {
      return 0;
    }
  }
  /* BV: LSHR --------------------------------------------------------------- */
  else if (tag == BZLA_BV_LSHR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SHR))
    {
      return 0;
    }
  }
  /* BV: ULT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_ULT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ULT))
    {
      return 0;
    }
  }
  /* BV: NAND --------------------------------------------------------------- */
  else if (tag == BZLA_BV_NAND_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NAND))
    {
      return 0;
    }
  }
  /* BV: NOR ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_NOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NOR))
    {
      return 0;
    }
  }
  /* BV: XNOR --------------------------------------------------------------- */
  else if (tag == BZLA_BV_XNOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_XNOR))
    {
      return 0;
    }
  }
  /* BV: COMP --------------------------------------------------------------- */
  else if (tag == BZLA_BV_COMP_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_COMP))
    {
      return 0;
    }
  }
  /* BV: SDIV --------------------------------------------------------------- */
  else if (tag == BZLA_BV_SDIV_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SDIV))
    {
      return 0;
    }
  }
  /* BV: SREM --------------------------------------------------------------- */
  else if (tag == BZLA_BV_SREM_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SREM))
    {
      return 0;
    }
  }
  /* BV: SMOD --------------------------------------------------------------- */
  else if (tag == BZLA_BV_SMOD_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SMOD))
    {
      return 0;
    }
  }
  /* BV: ASHR --------------------------------------------------------------- */
  else if (tag == BZLA_BV_ASHR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ASHR))
    {
      return 0;
    }
  }
  /* BV: REPEAT ------------------------------------------------------------- */
  else if (tag == BZLA_BV_REPEAT_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
    if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
    width = bitwuzla_term_bv_get_size(item_cur[1].exp);
    if (item_cur->num && ((uint32_t)(INT32_MAX / item_cur->num) < width))
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "resulting bit-width of 'repeat' too large");
    }
    exp = bitwuzla_mk_term1_indexed1(
        bitwuzla, BITWUZLA_KIND_BV_REPEAT, item_cur[1].exp, item_cur->num);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* BV: ZERO EXTEND -------------------------------------------------------- */
  else if (tag == BZLA_BV_ZERO_EXTEND_TAG_SMT2)
  {
    if (!close_term_extend_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ZERO_EXTEND))
    {
      return 0;
    }
  }
  /* BV: SIGN EXTEND -------------------------------------------------------- */
  else if (tag == BZLA_BV_SIGN_EXTEND_TAG_SMT2)
  {
    if (!close_term_extend_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SIGN_EXTEND))
    {
      return 0;
    }
  }
  /* BV: ROTATE LEFT -------------------------------------------------------- */
  else if (tag == BZLA_BV_ROTATE_LEFT_TAG_SMT2)
  {
    if (!close_term_rotate_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ROLI))
    {
      return 0;
    }
  }
  /* BV: ROTATE RIGHT ------------------------------------------------------- */
  else if (tag == BZLA_BV_ROTATE_RIGHT_TAG_SMT2)
  {
    if (!close_term_rotate_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_RORI))
    {
      return 0;
    }
  }
  /* BV: ULE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_ULE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ULE))
    {
      return 0;
    }
  }
  /* BV: UGT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_UGT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UGT))
    {
      return 0;
    }
  }
  /* BV: UGE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_UGE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UGE))
    {
      return 0;
    }
  }
  /* BV: SLT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SLT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SLT))
    {
      return 0;
    }
  }
  /* BV: SLE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SLE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SLE))
    {
      return 0;
    }
  }
  /* BV: SGT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SGT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SGT))
    {
      return 0;
    }
  }
  /* BV: SGE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SGE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SGE))
    {
      return 0;
    }
  }
  /* BV: SADDO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SADDO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SADD_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: UADDO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_UADDO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UADD_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: SDIVO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SDIVO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SDIV_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: SMULO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SMULO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SMUL_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: UMULO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_UMULO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UMUL_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: SSUBO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SSUBO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SSUB_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: USUBO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_USUBO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_USUB_OVERFLOW))
    {
      return 0;
    }
  }
  /* FP: (fp (_ BitVec 1) (_ BitVec n) (_ BitVec m)) -------------------- */
  else if (tag == BZLA_FP_FP_TAG_SMT2)
  {
    if (nargs < 3)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser, "argument to '%s' missing", item_cur->node->name);
    }
    for (i = 1; i <= nargs; i++)
    {
      if (!bitwuzla_term_is_bv(item_cur[i].exp))
      {
        return !perr_smt2(
            parser,
            "invalid argument to '%s', expected bit-vector expression",
            item_cur->node->name);
      }
    }
    if (bitwuzla_term_bv_get_size(item_cur[1].exp) != 1)
      return !perr_smt2(parser,
                        "first argument to '%s' invalid, expected "
                        "bit-vector sort of size 1",
                        item_cur->node->name);
    if (bitwuzla_term_is_bv_value(item_cur[1].exp)
        && bitwuzla_term_is_bv_value(item_cur[2].exp)
        && bitwuzla_term_is_bv_value(item_cur[3].exp))
    {
      exp = bitwuzla_mk_fp_value(
          bitwuzla, item_cur[1].exp, item_cur[2].exp, item_cur[3].exp);
    }
    else
    {
      exp = bitwuzla_mk_term3(bitwuzla,
                              BITWUZLA_KIND_FP_FP,
                              item_cur[1].exp,
                              item_cur[2].exp,
                              item_cur[3].exp);
    }
    assert(exp);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* FP: fp.abs ------------------------------------------------------------- */
  else if (tag == BZLA_FP_ABS_TAG_SMT2)
  {
    if (!close_term_unary_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_ABS))
    {
      return 0;
    }
  }
  /* FP: fp.neg ------------------------------------------------------------- */
  else if (tag == BZLA_FP_NEG_TAG_SMT2)
  {
    if (!close_term_unary_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_NEG))
    {
      return 0;
    }
  }
  /* FP: fp.sqrt ------------------------------------------------------------ */
  else if (tag == BZLA_FP_SQRT_TAG_SMT2)
  {
    if (!close_term_unary_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_SQRT))
    {
      return 0;
    }
  }
  /* FP: fp.roundToIntegral ------------------------------------------------- */
  else if (tag == BZLA_FP_ROUND_TO_INT_TAG_SMT2)
  {
    if (!close_term_unary_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_RTI))
    {
      return 0;
    }
  }
  /* FP: fp.add ------------------------------------------------------------- */
  else if (tag == BZLA_FP_ADD_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_ADD))
    {
      return 0;
    }
  }
  /* FP: fp.sub ------------------------------------------------------------- */
  else if (tag == BZLA_FP_SUB_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_SUB))
    {
      return 0;
    }
  }
  /* FP: fp.mul ------------------------------------------------------------- */
  else if (tag == BZLA_FP_MUL_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_MUL))
    {
      return 0;
    }
  }
  /* FP: fp.div ------------------------------------------------------------- */
  else if (tag == BZLA_FP_DIV_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_DIV))
    {
      return 0;
    }
  }
  /* FP: fp.fma ------------------------------------------------------------- */
  else if (tag == BZLA_FP_FMA_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 4)) return 0;
    if (!check_rm_fp_args_smt2(parser, item_cur, nargs)) return 0;
    if (!check_arg_sorts_match_smt2(parser, item_cur, 1, 3)) return 0;
    const BitwuzlaTerm *args[] = {
        item_cur[1].exp, item_cur[2].exp, item_cur[3].exp, item_cur[4].exp};
    exp = bitwuzla_mk_term(bitwuzla, BITWUZLA_KIND_FP_FMA, 4, args);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* FP: fp.rem ------------------------------------------------------------- */
  else if (tag == BZLA_FP_REM_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_REM))
    {
      return 0;
    }
  }
  /* FP: fp.min ------------------------------------------------------------- */
  else if (tag == BZLA_FP_MIN_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_MIN))
    {
      return 0;
    }
  }
  /* FP: fp.max ------------------------------------------------------------- */
  else if (tag == BZLA_FP_MAX_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_MAX))
    {
      return 0;
    }
  }
  /* FP: fp.eq -------------------------------------------------------------- */
  else if (tag == BZLA_FP_EQ_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_EQ))
    {
      return 0;
    }
  }
  /* FP: fp.leq ------------------------------------------------------------- */
  else if (tag == BZLA_FP_LEQ_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_LEQ))
    {
      return 0;
    }
  }
  /* FP: fp.lt -------------------------------------------------------------- */
  else if (tag == BZLA_FP_LT_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_LT))
    {
      return 0;
    }
  }
  /* FP: fp.geq ------------------------------------------------------------- */
  else if (tag == BZLA_FP_GEQ_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_GEQ))
    {
      return 0;
    }
  }
  /* FP: fp.gt -------------------------------------------------------------- */
  else if (tag == BZLA_FP_GT_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_GT))
    {
      return 0;
    }
  }
  /* FP: fp.isNormal -------------------------------------------------------- */
  else if (tag == BZLA_FP_IS_NORMAL_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_NORMAL))
    {
      return 0;
    }
  }
  /* FP: fp.isSubnormal ----------------------------------------------------- */
  else if (tag == BZLA_FP_IS_SUBNORMAL_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_SUBNORMAL))
    {
      return 0;
    }
  }
  /* FP: fp.isZero ---------------------------------------------------------- */
  else if (tag == BZLA_FP_IS_ZERO_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_ZERO))
    {
      return 0;
    }
  }
  /* FP: fp.isInfinite ------------------------------------------------------ */
  else if (tag == BZLA_FP_IS_INF_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_INF))
    {
      return 0;
    }
  }
  /* FP: fp.isNaN ----------------------------------------------------------- */
  else if (tag == BZLA_FP_IS_NAN_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_NAN))
    {
      return 0;
    }
  }
  /* FP: fp.isNegative ------------------------------------------------------ */
  else if (tag == BZLA_FP_IS_NEG_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_NEG))
    {
      return 0;
    }
  }
  /* FP: fp.isPositive ------------------------------------------------------ */
  else if (tag == BZLA_FP_IS_POS_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_POS))
    {
      return 0;
    }
  }
  /* FP: fp.to_sbv fp.to_ubv ------------------------------------------------ */
  else if (tag == BZLA_FP_TO_SBV_TAG_SMT2 || tag == BZLA_FP_TO_UBV_TAG_SMT2)
  {
    assert(item_cur->idx0);
    if (item_cur[1].tag != BZLA_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser, "expected expression");
    }
    if (!bitwuzla_term_is_rm(item_cur[1].exp))
    {
      return !perr_smt2(
          parser,
          "invalid argument to '%s', expected bit-vector expression",
          item_cur->node->name);
    }
    if (item_cur[2].tag != BZLA_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "expected expression");
    }
    if (!bitwuzla_term_is_fp(item_cur[2].exp))
    {
      return !perr_smt2(
          parser,
          "invalid argument to '%s', expected bit-vector expression",
          item_cur->node->name);
    }
    if (tag == BZLA_FP_TO_SBV_TAG_SMT2)
    {
      exp = bitwuzla_mk_term2_indexed1(bitwuzla,
                                       BITWUZLA_KIND_FP_TO_SBV,
                                       item_cur[1].exp,
                                       item_cur[2].exp,
                                       item_cur->idx0);
    }
    else
    {
      exp = bitwuzla_mk_term2_indexed1(bitwuzla,
                                       BITWUZLA_KIND_FP_TO_UBV,
                                       item_cur[1].exp,
                                       item_cur[2].exp,
                                       item_cur->idx0);
    }
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* FP: to_fp -------------------------------------------------------------- */
  else if (tag == BZLA_FP_TO_FP_TAG_SMT2)
  {
    if (nargs == 1)
    {
      /* (_ to_fp eb sb) (_ BitVec m) */
      if (item_cur[1].tag != BZLA_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[1].coo;
        return !perr_smt2(parser, "expected expression");
      }
      if (!bitwuzla_term_is_bv(item_cur[1].exp))
      {
        return !perr_smt2(
            parser,
            "invalid argument to '%s', expected bit-vector expression",
            item_cur->node->name);
      }
      assert(item_cur->idx0);
      assert(item_cur->idx1);
      exp = bitwuzla_mk_term1_indexed2(bitwuzla,
                                       BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                       item_cur[1].exp,
                                       item_cur->idx0,
                                       item_cur->idx1);
      release_exp_and_overwrite(parser, item_open, item_cur, exp);
    }
    else
    {
      close_term_to_fp_two_args(parser, item_open, item_cur, nargs);
    }
  }
  /* FP: to_fp_unsigned ----------------------------------------------------- */
  else if (tag == BZLA_FP_TO_FP_UNSIGNED_TAG_SMT2)
  {
    close_term_to_fp_two_args(parser, item_open, item_cur, nargs);
  }
  /* Real: / ---------------------------------------------------------------- */
  else if (tag == BZLA_REAL_DIV_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 2)) return 0;
    if (!check_real_arg_smt2(parser, item_cur, 1)) return 0;
    if (!check_real_arg_smt2(parser, item_cur, 2)) return 0;
    parser->work.top   = item_cur;
    item_open->tag     = BZLA_REAL_DIV_TAG_SMT2;
    item_open->node    = item_cur[0].node;
    item_open->strs[0] = item_cur[1].str;
    item_open->strs[1] = item_cur[2].str;
  }
  /* let (<var_binding>+) <term> -------------------------------------------- */
  else if (tag == BZLA_LET_TAG_SMT2)
  {
    for (i = 1; i < nargs; i++)
    {
      if (item_cur[i].tag != BZLA_SYMBOL_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        return !perr_smt2(parser, "expected symbol as argument %d of 'let'", i);
      }
    }
    if (item_cur[nargs].tag != BZLA_SYMBOL_TAG_SMT2)
    {
      if (item_cur[i].tag != BZLA_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        return !perr_smt2(
            parser, "expected expression as argument %d of 'let'", nargs);
      }
    }
    item_open[0].tag = BZLA_EXP_TAG_SMT2;
    item_open[0].exp = item_cur[nargs].exp;
    for (i = 1; i < nargs; i++)
    {
      assert(item_cur[i].tag == BZLA_SYMBOL_TAG_SMT2);
      sym = item_cur[i].node;
      assert(sym);
      assert(sym->coo.x);
      assert(sym->tag == BZLA_SYMBOL_TAG_SMT2);
      remove_symbol_smt2(parser, sym);
    }
    parser->work.top = item_cur;
  }
  /* <var_binding> ---------------------------------------------------------- */
  else if (tag == BZLA_LETBIND_TAG_SMT2)
  {
    assert(item_cur[1].tag == BZLA_SYMBOL_TAG_SMT2);
    if (nargs == 1)
      return !perr_smt2(
          parser, "term to be bound to '%s' missing", item_cur[1].node->name);
    if (nargs > 2)
    {
      parser->perrcoo = item_cur[3].coo;
      return !perr_smt2(
          parser, "second term bound to '%s'", item_cur[1].node->name);
    }
    if (item_cur[2].tag != BZLA_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "expected expression in 'let' var binding");
    }
    item_open[0] = item_cur[1];
    assert(!item_open[0].node->exp);
    assert(item_cur[2].tag == BZLA_EXP_TAG_SMT2);
    item_open[0].node->exp = item_cur[2].exp;
    assert(!item_open[0].node->bound);
    item_open[0].node->bound = 1;
    parser->work.top         = item_cur;
    assert(!parser->isvarbinding);
    parser->isvarbinding = true;
  }
  /* (<var_binding>+) ------------------------------------------------------- */
  else if (tag == BZLA_PARLETBINDING_TAG_SMT2)
  {
    assert(parser->isvarbinding);
    parser->isvarbinding = false;
#ifndef NDEBUG
    for (i = 1; i <= nargs; i++)
      assert(item_cur[i].tag == BZLA_SYMBOL_TAG_SMT2);
#endif
    for (i = 0; i < nargs; i++) item_open[i] = item_cur[i + 1];
    parser->work.top = item_open + nargs;
    assert(!parser->expecting_body);
    parser->expecting_body = "let";
  }
  /* forall (<sorted_var>+) <term> ------------------------------------------ */
  else if (tag == BZLA_FORALL_TAG_SMT2)
  {
    if (!close_term_quant(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FORALL))
    {
      return 0;
    }
  }
  /* exists (<sorted_var>+) <term> ------------------------------------------ */
  else if (tag == BZLA_EXISTS_TAG_SMT2)
  {
    if (!close_term_quant(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_EXISTS))
    {
      return 0;
    }
  }
  /* <sorted_var> ----------------------------------------------------------- */
  else if (tag == BZLA_SORTED_VAR_TAG_SMT2)
  {
    assert(item_cur[1].tag == BZLA_SYMBOL_TAG_SMT2);
    if (nargs != 1)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser,
                        "expected only one variable at sorted var '%s'",
                        item_cur[1].node->name);
    }
    parser->work.top = item_cur;
    item_open->tag   = BZLA_SYMBOL_TAG_SMT2;
    item_open->node  = item_cur[1].node;
    assert(bitwuzla_term_is_var(item_open->node->exp));
    assert(!parser->sorted_var);
    parser->sorted_var = 1;
  }
  /* (<sorted_var>+) -------------------------------------------------------- */
  else if (tag == BZLA_SORTED_VARS_TAG_SMT2)
  {
    assert(parser->sorted_var);
    parser->sorted_var = 0;
#ifndef NDEBUG
    for (i = 1; i <= nargs; i++)
    {
      assert(item_cur[i].tag == BZLA_SYMBOL_TAG_SMT2);
      assert(bitwuzla_term_is_var(item_cur[i].node->exp));
    }
#endif
    for (i = 0; i < nargs; i++) item_open[i] = item_cur[i + 1];
    parser->work.top = item_open + nargs;
    assert(!parser->expecting_body);
    parser->expecting_body = "quantifier";
  }
  /* DEFAULT: unsupported --------------------------------------------------- */
  else
  {
    // This should not occur, but we keep it as a bad style of
    // defensive programming for future extensions of the parser.
    parser->perrcoo = item_cur->coo;
    return !perr_smt2(
        parser,
        "internal parse error: can not close yet unsupported '%s'",
        item2str_smt2(item_cur));
  }
  assert(open > 0);
  parser->open = open - 1;

  return 1;
}

static int32_t
parse_open_term_quant(BzlaSMT2Parser *parser, const char *msg)
{
  assert(parser);
  assert(msg);

  if (!read_lpar_smt2(parser, msg)) return 0;
  push_item_smt2(parser, BZLA_LPAR_TAG_SMT2);
  parser->open++, assert(parser->open > 0);
  push_item_smt2(parser, BZLA_SORTED_VARS_TAG_SMT2);
  assert(!parser->sorted_var);
  parser->sorted_var       = 1;
  parser->need_quantifiers = true;
  return 1;
}

static int32_t
check_open_term_indexed(BzlaSMT2Parser *parser, BzlaSMT2Node *node)
{
  assert(parser);
  assert(node);

  if (BZLA_COUNT_STACK(parser->work) < 3)
  {
    assert(BZLA_COUNT_STACK(parser->work) == 2);
    assert(parser->work.start[0].tag == BZLA_LPAR_TAG_SMT2);
    assert(parser->work.start[1].tag == BZLA_UNDERSCORE_TAG_SMT2);
    parser->perrcoo = parser->work.start[0].coo;
    return !perr_smt2(parser, "expected '(' before '(_ %s'", node->name);
  }
  if (parser->work.top[-3].tag != BZLA_LPAR_TAG_SMT2)
  {
    parser->perrcoo = parser->work.top[-3].coo;
    return !perr_smt2(parser,
                      "expected '(' at '%s' before '(_ %s'",
                      item2str_smt2(parser->work.top - 3),
                      node->name);
  }
  return 1;
}

static int32_t
parse_open_term_indexed_parametric(BzlaSMT2Parser *parser,
                                   BzlaSMT2Item *item_cur,
                                   int32_t tag,
                                   uint32_t nargs,
                                   BzlaSMT2Node *node,
                                   const char *msg)
{
  assert(parser);
  assert(item_cur);
  assert(node);
  assert(msg);

  assert(nargs > 1 || BZLA_COUNT_STACK(parser->work) >= 2);

  BzlaSMT2Coo firstcoo;
  BzlaSMT2Item *item_open;

  if (!check_open_term_indexed(parser, node)) return 0;

  item_open = item_cur - 1;
  assert(node && tag == (int32_t) node->tag);

  if (nargs == 1)
  {
    if (tag == BZLA_FP_TO_SBV_TAG_SMT2 || tag == BZLA_FP_TO_UBV_TAG_SMT2)
    {
      if (!parse_bit_width_smt2(parser, &item_open->idx0)) return 0;
    }
    else
    {
      if (!parse_uint32_smt2(parser, true, &item_open->num)) return 0;
    }
  }
  else if (tag == BZLA_FP_TO_FP_TAG_SMT2
           || tag == BZLA_FP_TO_FP_UNSIGNED_TAG_SMT2)
  {
    assert(nargs == 2);
    if (!parse_uint32_smt2(parser, true, &item_open->idx0)) return 0;
    if (item_open->idx0 <= 1)
    {
      return !perr_smt2(
          parser,
          "expected positive 32 bit integer > 1 for exponent size, got '%u'",
          item_open->idx0);
    }
    if (!parse_uint32_smt2(parser, true, &item_open->idx1)) return 0;
    if (item_open->idx1 <= 1)
    {
      return !perr_smt2(
          parser,
          "expected positive 32 bit integer > 1 for significand size, got '%u'",
          item_open->idx1);
    }
  }
  else
  {
    assert(nargs == 2);
    if (!parse_uint32_smt2(parser, true, &item_open->idx0)) return 0;
    firstcoo = parser->coo;
    if (!parse_uint32_smt2(parser, true, &item_open->idx1)) return 0;
    if (tag == BZLA_BV_EXTRACT_TAG_SMT2 && item_open->idx0 < item_open->idx1)
    {
      parser->perrcoo = firstcoo;
      return !perr_smt2(parser,
                        "first parameter '%u' of '(_ extract' "
                        "smaller than second '%u'",
                        item_open->idx0,
                        item_open->idx1);
    }
  }

  item_open->tag   = tag;
  item_open->node  = node;
  parser->work.top = item_cur;
  if (!read_rpar_smt2(parser, msg)) return 0;
  assert(parser->open > 0);
  parser->open--;
  return 1;
}

static int32_t
parse_open_close_term_indexed_fp_special_const(
    BzlaSMT2Parser *parser,
    BzlaSMT2Item *item_cur,
    int32_t tag,
    BzlaSMT2Node *node,
    const char *msg,
    const BitwuzlaTerm *(*fun)(Bitwuzla *, const BitwuzlaSort *) )
{
  assert(parser);
  assert(item_cur);
  assert(node);
  assert(msg);

  assert(tag == BZLA_FP_POS_ZERO_TAG_SMT2 || tag == BZLA_FP_NEG_ZERO_TAG_SMT2
         || tag == BZLA_FP_POS_INF_TAG_SMT2 || tag == BZLA_FP_NEG_INF_TAG_SMT2
         || tag == BZLA_FP_NAN_TAG_SMT2);
  (void) tag;

  Bitwuzla *bitwuzla = parser->bitwuzla;
  BzlaSMT2Item *item_open = item_cur - 1;
  assert(node && tag == (int32_t) node->tag);
  if (!parse_uint32_smt2(parser, true, &item_open->idx0)) return 0;
  if (item_open->idx0 <= 1)
  {
    return !perr_smt2(
        parser,
        "expected positive 32 bit integer > 1 for exponent size, got '%u'",
        item_open->idx0);
  }
  if (!parse_uint32_smt2(parser, true, &item_open->idx1)) return 0;
  if (item_open->idx1 <= 1)
  {
    return !perr_smt2(
        parser,
        "expected positive 32 bit integer > 1 for significand size, got '%u'",
        item_open->idx1);
  }

  const BitwuzlaSort *sort =
      bitwuzla_mk_fp_sort(bitwuzla, item_open->idx0, item_open->idx1);
  const BitwuzlaTerm *exp = fun(bitwuzla, sort);

  item_open->tag   = BZLA_EXP_TAG_SMT2;
  item_open->node  = node;
  item_open->exp   = exp;
  parser->work.top = item_cur;
  if (!read_rpar_smt2(parser, msg)) return 0;
  assert(parser->open > 0);
  parser->open--;
  return 1;
}

static int32_t
parse_open_term_indexed(BzlaSMT2Parser *parser, BzlaSMT2Item *item_cur)
{
  assert(parser);
  assert(item_cur);

  uint32_t width, width2;
  int32_t tag;
  BzlaSMT2Node *node;
  const BitwuzlaTerm *exp;
  const BitwuzlaSort *s;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  if (!prev_item_was_lpar_smt2(parser)) return 0;

  tag  = read_token_smt2(parser);
  node = parser->last_node;

  if (tag == BZLA_INVALID_TAG_SMT2) return 0;
  if (tag == EOF) return !perr_smt2(parser, "unexpected end-of-file after '_'");

  if (tag == BZLA_BV_REPEAT_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 1, node, " to close '(_ repeat'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_BV_ZERO_EXTEND_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 1, node, " to close '(_ zero_extend'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_BV_SIGN_EXTEND_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 1, node, " to close '(_ sign_extend'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_BV_ROTATE_LEFT_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 1, node, " to close '(_ rotate_left'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_BV_ROTATE_RIGHT_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 1, node, " to close '(_ rotate_right'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_BV_EXTRACT_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 2, node, " to close '(_ extract'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_POS_ZERO_TAG_SMT2)
  {
    if (!parse_open_close_term_indexed_fp_special_const(
            parser,
            item_cur,
            tag,
            node,
            " to close '(_ +zero'",
            bitwuzla_mk_fp_pos_zero))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_NEG_ZERO_TAG_SMT2)
  {
    if (!parse_open_close_term_indexed_fp_special_const(
            parser,
            item_cur,
            tag,
            node,
            " to close '(_ -zero'",
            bitwuzla_mk_fp_neg_zero))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_POS_INF_TAG_SMT2)
  {
    if (!parse_open_close_term_indexed_fp_special_const(parser,
                                                        item_cur,
                                                        tag,
                                                        node,
                                                        " to close '(_ +oo'",
                                                        bitwuzla_mk_fp_pos_inf))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_NEG_INF_TAG_SMT2)
  {
    if (!parse_open_close_term_indexed_fp_special_const(parser,
                                                        item_cur,
                                                        tag,
                                                        node,
                                                        " to close '(_ -oo'",
                                                        bitwuzla_mk_fp_neg_inf))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_NAN_TAG_SMT2)
  {
    if (!parse_open_close_term_indexed_fp_special_const(parser,
                                                        item_cur,
                                                        tag,
                                                        node,
                                                        " to close '(_ NaN'",
                                                        bitwuzla_mk_fp_nan))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_TO_SBV_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 1, node, " to close '(_ fp.to_sbv'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_TO_UBV_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 1, node, " to close '(_ fp.to_ubv'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_TO_FP_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 2, node, " to close '(_ to_fp'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_FP_TO_FP_UNSIGNED_TAG_SMT2)
  {
    if (!parse_open_term_indexed_parametric(
            parser, item_cur, tag, 2, node, " to close '(_ to_fp_unsigned'"))
    {
      return 0;
    }
  }
  else if (tag == BZLA_SYMBOL_TAG_SMT2
           && is_bvconst_str_smt2(parser->token.start))
  {
    char *constr, *decstr;
    BzlaSMT2Coo coo;
    exp    = 0;
    decstr = bzla_mem_strdup(parser->mem, parser->token.start + 2);
    constr = bzla_util_dec_to_bin_str(parser->mem, parser->token.start + 2);
    coo    = parser->coo;
    coo.y += 2;
    if (parse_uint32_smt2(parser, false, &width))
    {
      width2 = strlen(constr);
      if (width2 > width)
      {
        parser->perrcoo = coo;
        (void) perr_smt2(parser,
                         "decimal constant '%s' needs %d bits which "
                         "exceeds bit-width '%d'",
                         decstr,
                         width2,
                         width);
      }
      else if (width2 == width)
      {
        s   = bitwuzla_mk_bv_sort(bitwuzla, width);
        exp = bitwuzla_mk_bv_value(bitwuzla, s, constr, BITWUZLA_BV_BASE_BIN);
      }
      else if (!width2)
      {
        s   = bitwuzla_mk_bv_sort(bitwuzla, width);
        exp = bitwuzla_mk_bv_zero(bitwuzla, s);
      }
      else
      {
        BzlaBitVector *constrbv = 0, *uconstrbv;
        uint32_t w              = width - width2;
        char *uconstr;
        if (!strcmp(constr, ""))
        {
          uconstrbv = bzla_bv_new(parser->mem, w);
        }
        else
        {
          constrbv  = bzla_bv_char_to_bv(parser->mem, constr);
          uconstrbv = bzla_bv_uext(parser->mem, constrbv, w);
        }
        uconstr = bzla_bv_to_char(parser->mem, uconstrbv);
        s       = bitwuzla_mk_bv_sort(bitwuzla, strlen(uconstr));
        exp = bitwuzla_mk_bv_value(bitwuzla, s, uconstr, BITWUZLA_BV_BASE_BIN);
        bzla_mem_freestr(parser->mem, uconstr);
        bzla_bv_free(parser->mem, uconstrbv);
        if (constrbv) bzla_bv_free(parser->mem, constrbv);
      }
    }
    bzla_mem_freestr(parser->mem, decstr);
    bzla_mem_freestr(parser->mem, constr);
    if (!exp) return 0;
    assert(bitwuzla_term_bv_get_size(exp) == width);
    assert(item_cur > parser->work.start);
    item_cur--, parser->work.top--;
    assert(item_cur->tag == BZLA_LPAR_TAG_SMT2);
    assert(parser->open > 0);
    parser->open--;
    item_cur->tag = BZLA_EXP_TAG_SMT2;
    item_cur->exp = exp;
    if (!read_rpar_smt2(parser, " to close '(_ bv..'")) return 0;
  }
  else
  {
    return !perr_smt2(
        parser, "invalid parametric term '_ %s'", parser->token.start);
  }
  return 1;
}

static int32_t
parse_open_term_as(BzlaSMT2Parser *parser, BzlaSMT2Item *item_cur)
{
  assert(parser);
  assert(item_cur);

  const char *identifier;
  int32_t tag;
  BzlaSMT2Node *node;
  BzlaSMT2Item *item_open;

  if (!prev_item_was_lpar_smt2(parser)) return 0;

  if (BZLA_COUNT_STACK(parser->work) < 3)
  {
    assert(BZLA_COUNT_STACK(parser->work) == 2);
    assert(parser->work.start[0].tag == BZLA_LPAR_TAG_SMT2);
    assert(parser->work.start[1].tag == BZLA_UNDERSCORE_TAG_SMT2);
    parser->perrcoo = parser->work.start[0].coo;
    return !perr_smt2(parser, "expected '(' before '(as'");
  }
  if (parser->work.top[-3].tag != BZLA_LPAR_TAG_SMT2)
  {
    parser->perrcoo = parser->work.top[-3].coo;
    return !perr_smt2(parser,
                      "expected '(' at '%s' before '(as'",
                      item2str_smt2(parser->work.top - 3));
  }

  tag  = read_token_smt2(parser);
  node = parser->last_node;

  if (tag == BZLA_INVALID_TAG_SMT2) return 0;
  if (tag == EOF) return !perr_smt2(parser, "unexpected end-of-file after '_'");
  if (tag != BZLA_SYMBOL_TAG_SMT2)
  {
    return !perr_smt2(parser, "expected identifier");
  }

  identifier = node->name;
  item_open  = item_cur - 1;

  if (!strcmp(identifier, "const"))
  {
    tag = read_token_smt2(parser);
    if (!parse_sort(parser, tag, true, &item_open->sort)) return 0;
    assert(item_open->sort);
  }
  else
  {
    return !perr_smt2(parser, "invalid identifier '%s'", identifier);
  }

  item_open->tag   = BZLA_AS_TAG_SMT2;
  parser->work.top = item_cur;
  if (!read_rpar_smt2(parser, " to close (as ")) return 0;
  assert(parser->open > 0);
  parser->open--;
  return 1;
}

static int32_t
parse_open_term_item_with_node(BzlaSMT2Parser *parser,
                               int32_t tag,
                               BzlaSMT2Item *item_cur)
{
  assert(parser);
  assert(item_cur);

  Bitwuzla *bitwuzla = parser->bitwuzla;

  item_cur->node = parser->last_node;

  if (tag & BZLA_COMMAND_TAG_CLASS_SMT2)
  {
    return !perr_smt2(parser, "unexpected command '%s'", item_cur->node->name);
  }
  if (tag & BZLA_KEYWORD_TAG_CLASS_SMT2)
  {
    return !perr_smt2(parser, "unexpected keyword '%s'", item_cur->node->name);
  }
  if (tag & BZLA_RESERVED_TAG_CLASS_SMT2)
  {
    if (tag == BZLA_LET_TAG_SMT2)
    {
      if (!read_lpar_smt2(parser, " after 'let'")) return 0;
      push_item_smt2(parser, BZLA_LPAR_TAG_SMT2);
      parser->open++, assert(parser->open > 0);
      push_item_smt2(parser, BZLA_PARLETBINDING_TAG_SMT2);
      assert(!parser->isvarbinding);
      parser->isvarbinding = true;
    }
    else if (tag == BZLA_FORALL_TAG_SMT2)
    {
      if (!parse_open_term_quant(parser, " after 'forall'")) return 0;
    }
    else if (tag == BZLA_EXISTS_TAG_SMT2)
    {
      if (!parse_open_term_quant(parser, " after 'exists'")) return 0;
    }
    else if (tag == BZLA_UNDERSCORE_TAG_SMT2)
    {
      if (!parse_open_term_indexed(parser, item_cur)) return 0;
    }
    else if (tag == BZLA_AS_TAG_SMT2)
    {
      if (!parse_open_term_as(parser, item_cur)) return 0;
    }
    else if (tag == BZLA_BANG_TAG_SMT2)
    {
      if (!prev_item_was_lpar_smt2(parser)) return 0;
      item_cur->tag = BZLA_BANG_TAG_SMT2;
    }
    else
    {
      assert(item_cur->node->name);
      return !perr_smt2(
          parser, "unsupported reserved word '%s'", item_cur->node->name);
    }
  }
  else if (tag == BZLA_SYMBOL_TAG_SMT2)
  {
    assert(item_cur->node);
    if (!item_cur->node->exp)
      return !perr_smt2(parser, "undefined symbol '%s'", item_cur->node->name);
    item_cur->tag = BZLA_EXP_TAG_SMT2;
    item_cur->exp = item_cur->node->exp;
  }
  else if (tag == BZLA_TRUE_TAG_SMT2)
  {
    item_cur->tag = BZLA_EXP_TAG_SMT2;
    item_cur->exp = bitwuzla_mk_true(bitwuzla);
  }
  else if (tag == BZLA_FALSE_TAG_SMT2)
  {
    item_cur->tag = BZLA_EXP_TAG_SMT2;
    item_cur->exp = bitwuzla_mk_false(bitwuzla);
  }
  else if (tag == BZLA_ATTRIBUTE_TAG_SMT2)
  {
    return !perr_smt2(parser, "unexpected attribute '%s'", parser->token.start);
  }
  else if (tag & BZLA_CORE_TAG_CLASS_SMT2)
  {
    if (tag == BZLA_BOOL_TAG_SMT2)
      return !perr_smt2(parser, "unexpected 'Bool'");
  }
  else if (tag & BZLA_ARRAY_TAG_CLASS_SMT2)
  {
    if (tag == BZLA_ARRAY_TAG_SMT2)
      return !perr_smt2(parser, "unexpected 'Array'");
  }
  else if (tag & BZLA_BV_TAG_CLASS_SMT2)
  {
    if (tag == BZLA_BV_BITVEC_TAG_SMT2)
      return !perr_smt2(parser, "unexpected 'BitVec'");
  }
  else if (tag & BZLA_FP_TAG_CLASS_SMT2)
  {
    if (tag == BZLA_FP_FLOATINGPOINT_TAG_SMT2 || tag == BZLA_FP_FLOAT16_TAG_SMT2
        || tag == BZLA_FP_FLOAT32_TAG_SMT2 || tag == BZLA_FP_FLOAT64_TAG_SMT2
        || tag == BZLA_FP_FLOAT128_TAG_SMT2)
      return !perr_smt2(parser, "unexpected '%s'", parser->token.start);

    if (tag == BZLA_FP_ROUNDINGMODE_NEAREST_TO_EVEN_TAG_SMT2
        || tag == BZLA_FP_ROUNDINGMODE_RNE_TAG_SMT2)
    {
      item_cur->tag = BZLA_EXP_TAG_SMT2;
      item_cur->exp = bitwuzla_mk_rm_value(bitwuzla, BITWUZLA_RM_RNE);
    }
    else if (tag == BZLA_FP_ROUNDINGMODE_NEAREST_TO_AWAY_TAG_SMT2
             || tag == BZLA_FP_ROUNDINGMODE_RNA_TAG_SMT2)
    {
      item_cur->tag = BZLA_EXP_TAG_SMT2;
      item_cur->exp = bitwuzla_mk_rm_value(bitwuzla, BITWUZLA_RM_RNA);
    }
    else if (tag == BZLA_FP_ROUNDINGMODE_TOWARD_POSITIVE_TAG_SMT2
             || tag == BZLA_FP_ROUNDINGMODE_RTP_TAG_SMT2)
    {
      item_cur->tag = BZLA_EXP_TAG_SMT2;
      item_cur->exp = bitwuzla_mk_rm_value(bitwuzla, BITWUZLA_RM_RTP);
    }
    else if (tag == BZLA_FP_ROUNDINGMODE_TOWARD_NEGATIVE_TAG_SMT2
             || tag == BZLA_FP_ROUNDINGMODE_RTN_TAG_SMT2)
    {
      item_cur->tag = BZLA_EXP_TAG_SMT2;
      item_cur->exp = bitwuzla_mk_rm_value(bitwuzla, BITWUZLA_RM_RTN);
    }
    else if (tag == BZLA_FP_ROUNDINGMODE_TOWARD_ZERO_TAG_SMT2
             || tag == BZLA_FP_ROUNDINGMODE_RTZ_TAG_SMT2)
    {
      item_cur->tag = BZLA_EXP_TAG_SMT2;
      item_cur->exp = bitwuzla_mk_rm_value(bitwuzla, BITWUZLA_RM_RTZ);
    }
  }
  else if (tag != BZLA_REAL_DIV_TAG_SMT2)
  {
    return !perr_smt2(parser, "unexpected token '%s'", item2str_smt2(item_cur));
  }
  return 1;
}

static int32_t
parse_open_term(BzlaSMT2Parser *parser, int32_t tag)
{
  assert(parser);

  uint32_t width, width2;
  BzlaSMT2Item *item_cur;
  BzlaSMT2Node *sym, *new_sym;
  const BitwuzlaSort *s;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  sym     = 0;
  new_sym = 0;

  if (parser->expecting_body) parser->expecting_body = 0;

  item_cur = push_item_smt2(parser, tag);

  if (tag == BZLA_LPAR_TAG_SMT2)
  {
    BzlaSMT2Item *q;
    if (parser->isvarbinding)
    {
      push_item_smt2(parser, BZLA_LETBIND_TAG_SMT2);
      parser->isvarbinding = false;

      tag = read_token_smt2(parser);

      if (tag == BZLA_INVALID_TAG_SMT2) return 0;
      if (tag == EOF)
        return !perr_smt2(parser,
                          "expected symbol to be bound after '(' at line %d "
                          "column %d but reached end-of-file",
                          item_cur->coo.x,
                          item_cur->coo.y);

      if (tag != BZLA_SYMBOL_TAG_SMT2)
        return !perr_smt2(parser,
                          "expected symbol to be bound at '%s' after '(' at "
                          "line %d column %d",
                          parser->token.start,
                          item_cur->coo.x,
                          item_cur->coo.y);
      sym = parser->last_node;
      assert(sym);
      /* shadow previously defined symbols */
      if (sym->coo.x)
      {
        new_sym       = new_node_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
        new_sym->name = bzla_mem_strdup(parser->mem, sym->name);
        /* symbol may already be in symbol table */
        insert_symbol_smt2(parser, new_sym);
        sym = new_sym;
      }
      sym->coo = parser->coo;
      q        = push_item_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
      q->node  = sym;
    }
    /* parse <sorted_var>: <symbol> <sort> */
    else if (parser->sorted_var)
    {
      push_item_smt2(parser, BZLA_SORTED_VAR_TAG_SMT2);
      parser->sorted_var = 0;
      s                  = 0;
      if (!read_symbol(parser, " in sorted var after '('", &sym)) return 0;
      assert(sym && sym->tag == BZLA_SYMBOL_TAG_SMT2);
      /* shadow previously defined symbols */
      if (sym->coo.x)
      {
        new_sym       = new_node_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
        new_sym->name = bzla_mem_strdup(parser->mem, sym->name);
        /* symbol may already be in symbol table */
        insert_symbol_smt2(parser, new_sym);
        sym = new_sym;
      }
      sym->coo = parser->coo;

      tag = read_token_smt2(parser);
      if (!parse_sort(parser, tag, false, &s)) return 0;

      q       = push_item_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
      q->node = sym;
      sym->exp = bitwuzla_mk_var(bitwuzla, s, sym->name);
    }
    parser->open++;
  }
  else if (parser->isvarbinding)
  {
    return !perr_smt2(
        parser, "expected var binding at '%s'", parser->token.start);
  }
  else if (parser->sorted_var)
  {
    return !perr_smt2(
        parser, "expected sorted variable at '%s'", parser->token.start);
  }
  else if (tag == BZLA_NAMED_TAG_SMT2)
  {
    BzlaSMT2Item *q;
    if (!read_symbol(parser, " after :named attribute", &sym))
    {
      return 0;
    }
    assert(sym);
    if (sym->coo.x)
    {
      return !perr_smt2(parser,
                        "symbol '%s' already defined at line %d column %d",
                        sym->name,
                        sym->coo.x,
                        sym->coo.y);
    }
    sym->coo = parser->coo;
    q        = push_item_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
    q->node  = sym;
  }
  else if (is_item_with_node_smt2(item_cur))
  {
    if (!parse_open_term_item_with_node(parser, tag, item_cur)) return 0;
  }
  else if (tag == BZLA_BINARY_CONSTANT_TAG_SMT2)
  {
    item_cur->tag = BZLA_EXP_TAG_SMT2;
    s = bitwuzla_mk_bv_sort(bitwuzla, strlen(parser->token.start + 2));
    item_cur->exp = bitwuzla_mk_bv_value(
        bitwuzla, s, parser->token.start + 2, BITWUZLA_BV_BASE_BIN);
  }
  else if (tag == BZLA_HEXADECIMAL_CONSTANT_TAG_SMT2)
  {
    char *constr, *uconstr;
    BzlaBitVector *constrbv = 0, *uconstrbv;
    constr = bzla_util_hex_to_bin_str(parser->mem, parser->token.start + 2);
    width2 = strlen(constr);
    width  = strlen(parser->token.start + 2) * 4;
    assert(width2 <= width);
    uint32_t w = width - width2;
    if (width2 == width)
    {
      uconstr = bzla_mem_strdup(parser->mem, constr);
    }
    else
    {
      if (!strcmp(constr, ""))
        uconstrbv = bzla_bv_new(parser->mem, w);
      else
      {
        constrbv  = bzla_bv_char_to_bv(parser->mem, constr);
        uconstrbv = bzla_bv_uext(parser->mem, constrbv, w);
      }
      uconstr = bzla_bv_to_char(parser->mem, uconstrbv);
      bzla_bv_free(parser->mem, uconstrbv);
      if (constrbv) bzla_bv_free(parser->mem, constrbv);
    }
    item_cur->tag = BZLA_EXP_TAG_SMT2;
    s             = bitwuzla_mk_bv_sort(bitwuzla, strlen(uconstr));
    item_cur->exp =
        bitwuzla_mk_bv_value(bitwuzla, s, uconstr, BITWUZLA_BV_BASE_BIN);
    bzla_mem_freestr(parser->mem, uconstr);
    bzla_mem_freestr(parser->mem, constr);
  }
  else if (tag == BZLA_DECIMAL_CONSTANT_TAG_SMT2
           || tag == BZLA_REAL_CONSTANT_TAG_SMT2)
  {
    item_cur->str = bzla_mem_strdup(parser->mem, parser->token.start);
  }
  else
  {
    return !perr_smt2(parser, "unexpected token '%s'", parser->token.start);
  }

  return 1;
}

/* Note: we need look ahead and tokens string only for get-value
 *       (for parsing a term list and printing the originally parsed,
 *       non-simplified expression) */
static int32_t
parse_term_aux_smt2(BzlaSMT2Parser *parser,
                    bool have_look_ahead,
                    int32_t look_ahead,
                    const BitwuzlaTerm **resptr,
                    BzlaSMT2Coo *cooptr)
{
  size_t work_cnt;
  int32_t tag;
  const BitwuzlaTerm *res;
  BzlaSMT2Item *l, *p;

  parser->open = 0;

  work_cnt = BZLA_COUNT_STACK(parser->work);

  do
  {
    if (have_look_ahead)
    {
      tag             = look_ahead;
      have_look_ahead = false;
    }
    else
      tag = read_token_smt2(parser);

    if (tag == BZLA_INVALID_TAG_SMT2)
    {
      assert(parser->error);
      return 0;
    }
    if (tag == EOF)
    {
      l = last_lpar_smt2(parser);
      if (!l)
        return !perr_smt2(parser,
                          "expected expression but reached end-of-file");
      return !perr_smt2(
          parser,
          "unexpected end-of-file, '(' at line %d column %d not closed",
          l->coo.x,
          l->coo.y);
    }

    /* ------------------------------------------------------------------- */
    /* close term                                                          */
    /* ------------------------------------------------------------------- */
    if (tag == BZLA_RPAR_TAG_SMT2)
    {
      if (!close_term(parser)) return 0;
    }
    /* ------------------------------------------------------------------- */
    /* parse term                                                          */
    /* ------------------------------------------------------------------- */
    else
    {
      if (!parse_open_term(parser, tag)) return 0;
    }
  } while (parser->open);
  if (BZLA_COUNT_STACK(parser->work) - work_cnt != 1)
  {
    // This should not occur, but we keep it as a bad style of
    // defensive programming for future extensions of the parser.
    return !perr_smt2(parser,
                      "internal parse error: worker stack of size %d",
                      BZLA_COUNT_STACK(parser->work));
  }
  p = parser->work.top - 1;
  if (p->tag != BZLA_EXP_TAG_SMT2)
  {
    parser->perrcoo = p->coo;
    return !perr_smt2(
        parser,
        "internal parse error: failed to translate parsed term at '%s'",
        item2str_smt2(p));
  }
  parser->work.top -= 1;
  res     = p->exp;
  *cooptr = p->coo;
  release_item_smt2(parser, p);
  assert(BZLA_COUNT_STACK(parser->work) == work_cnt);
  *resptr = res;
  return 1;
}

/* -------------------------------------------------------------------------- */

static int32_t
parse_term_smt2(BzlaSMT2Parser *parser,
                const BitwuzlaTerm **resptr,
                BzlaSMT2Coo *cooptr)
{
  return parse_term_aux_smt2(parser, false, 0, resptr, cooptr);
}

/*
 * skiptokens = 1 -> skip BZLA_LPAR_TAG_SMT2
 * skiptokens = 2 -> skip BZLA_UNDERSCORE_TAG_SMT2
 */
static int32_t
parse_bv_or_fp_sort(BzlaSMT2Parser *parser,
                    uint32_t skiptokens,
                    const BitwuzlaSort **resptr)
{
  assert(skiptokens <= 2);

  int32_t tag;
  uint32_t width = 0, width_eb = 0, width_sb = 0;
  char *msg;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  if (skiptokens < 1 && !read_lpar_smt2(parser, 0))
  {
    return 0;
  }
  if (skiptokens < 2)
  {
    tag = read_token_smt2(parser);
    if (tag == EOF)
      return !perr_smt2(parser, "expected '_' but reached end-of-file");
    if (tag != BZLA_UNDERSCORE_TAG_SMT2)
      return !perr_smt2(parser, "expected '_' at '%s'", parser->token.start);
  }

  tag = read_token_smt2(parser);
  if (tag == BZLA_INVALID_TAG_SMT2)
  {
    return 0;
  }
  if (tag == EOF)
  {
    return !perr_smt2(
        parser, "expected 'BitVec' or 'FloatingPoint' but reached end-of-file");
  }
  if (tag != BZLA_BV_BITVEC_TAG_SMT2 && tag != BZLA_FP_FLOATINGPOINT_TAG_SMT2)
  {
    return !perr_smt2(parser,
                      "expected 'BitVec' or 'FloatingPoint' at '%s'",
                      parser->token.start);
  }
  if (tag == BZLA_FP_FLOATINGPOINT_TAG_SMT2)
  {
    if (!parse_uint32_smt2(parser, true, &width_eb)) return 0;
    if (width_eb <= 1)
    {
      return !perr_smt2(
          parser,
          "expected positive 32 bit integer > 1 for exponent size, got '%u'",
          width_eb);
    }
    if (!parse_uint32_smt2(parser, true, &width_sb)) return 0;
    if (width_sb <= 1)
    {
      return !perr_smt2(
          parser,
          "expected positive 32 bit integer > 1 for significand size, got '%u'",
          width_sb);
    }
    BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
             3,
             "parsed floating-point sort of exponent width %d "
             "and significand width %d",
             width_eb,
             width_sb);
    *resptr = bitwuzla_mk_fp_sort(bitwuzla, width_eb, width_sb);
    msg     = " to close floating-point sort";
  }
  else
  {
    if (!parse_bit_width_smt2(parser, &width))
    {
      return 0;
    }
    BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
             3,
             "parsed bit-vector sort of width %d",
             width);
    *resptr = bitwuzla_mk_bv_sort(bitwuzla, width);
    msg     = " to close bit-vector sort";
  }

  BZLA_PUSH_STACK(parser->sorts, *resptr);

  return read_rpar_smt2(parser, msg);
}

static int32_t
parse_array_sort(BzlaSMT2Parser *parser, int32_t tag, const BitwuzlaSort **sort)
{
  const BitwuzlaSort *index, *value;
  if (tag == BZLA_ARRAY_TAG_SMT2)
  {
    tag = read_token_smt2(parser);
    if (!parse_sort(parser, tag, false, &index)) return 0;
    tag = read_token_smt2(parser);
    if (!parse_sort(parser, tag, false, &value)) return 0;
    if (!read_rpar_smt2(parser, " after element sort of Array")) return 0;
    *sort = bitwuzla_mk_array_sort(parser->bitwuzla, index, value);
    BZLA_PUSH_STACK(parser->sorts, *sort);
    return 1;
  }
  else if (tag == EOF)
    return !perr_smt2(parser, "reached end-of-file but expected 'Array'");
  return !perr_smt2(parser, "expected 'Array' at '%s'", parser->token.start);
}

static int32_t
parse_sort(BzlaSMT2Parser *parser,
           int32_t tag,
           bool allow_array_sort,
           const BitwuzlaSort **sort)
{
  BzlaSMT2Node *alias;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  if (tag == BZLA_BOOL_TAG_SMT2)
  {
    *sort = bitwuzla_mk_bool_sort(bitwuzla);
    BZLA_PUSH_STACK(parser->sorts, *sort);
    return 1;
  }
  else if (tag == BZLA_FP_FLOAT16_TAG_SMT2)
  {
    *sort = bitwuzla_mk_fp_sort(bitwuzla, 5, 11);
    BZLA_PUSH_STACK(parser->sorts, *sort);
    return 1;
  }
  else if (tag == BZLA_FP_FLOAT32_TAG_SMT2)
  {
    *sort = bitwuzla_mk_fp_sort(bitwuzla, 8, 24);
    BZLA_PUSH_STACK(parser->sorts, *sort);
    return 1;
  }
  else if (tag == BZLA_FP_FLOAT64_TAG_SMT2)
  {
    *sort = bitwuzla_mk_fp_sort(bitwuzla, 11, 53);
    BZLA_PUSH_STACK(parser->sorts, *sort);
    return 1;
  }
  else if (tag == BZLA_FP_FLOAT128_TAG_SMT2)
  {
    *sort = bitwuzla_mk_fp_sort(bitwuzla, 15, 113);
    BZLA_PUSH_STACK(parser->sorts, *sort);
    return 1;
  }
  else if (tag == BZLA_FP_ROUNDINGMODE_TAG_SMT2)
  {
    *sort = bitwuzla_mk_rm_sort(bitwuzla);
    BZLA_PUSH_STACK(parser->sorts, *sort);
    return 1;
  }
  else if (tag == BZLA_LPAR_TAG_SMT2)
  {
    if (allow_array_sort)
    {
      tag = read_token_smt2(parser);
      if (tag == BZLA_ARRAY_TAG_SMT2)
      {
        return parse_array_sort(parser, tag, sort);
      }
      else
      {
        if (tag == EOF)
          return !perr_smt2(parser,
                            "expected '_' or 'Array' but reached end-of-file");
        if (tag != BZLA_UNDERSCORE_TAG_SMT2)
          return !perr_smt2(
              parser, "expected '_' or 'Array' at '%s'", parser->token.start);
        return parse_bv_or_fp_sort(parser, 2, sort);
      }
    }
    else
      return parse_bv_or_fp_sort(parser, 1, sort);
  }
  else if (tag == BZLA_SYMBOL_TAG_SMT2)
  {
    alias = find_symbol_smt2(parser, parser->token.start);
    if (!alias || !alias->sort)
      return !perr_smt2(parser, "invalid sort '%s'", parser->token.start);
    *sort = alias->sort_alias;
    return 1;
  }
  else if (tag == EOF)
    return !perr_smt2(parser,
                      "reached end-of-file but expected '(' or sort keyword");
  return !perr_smt2(
      parser, "expected '(' or sort keyword at '%s'", parser->token.start);
}

static int32_t
declare_fun_smt2(BzlaSMT2Parser *parser, bool isconst)
{
  uint32_t i;
  int32_t tag;
  bool is_bool_var = false;
  BitwuzlaSortConstPtrStack args;
  BzlaSMT2Node *fun;
  fun = 0;
  const BitwuzlaSort *sort, *s;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  if (!read_symbol(parser,
                   isconst ? " after 'declare-const'" : " after 'declare-fun'",
                   &fun))
  {
    return 0;
  }

  assert(fun && fun->tag == BZLA_SYMBOL_TAG_SMT2);

  if (fun->coo.x)
    return !perr_smt2(parser,
                      "symbol '%s' already defined at line %d column %d",
                      fun->name,
                      fun->coo.x,
                      fun->coo.y);
  fun->coo = parser->coo;

  BZLA_INIT_STACK(parser->mem, args);

  if (!isconst)
  {
    if (!read_lpar_smt2(parser,
                        isconst ? " after const name" : " after function name"))
    {
      BZLA_RELEASE_STACK(args);
      return 0;
    }

    do
    {
      tag = read_token_smt2(parser);
      if (tag != BZLA_RPAR_TAG_SMT2)
      {
        if (!parse_sort(parser, tag, false, &sort))
        {
          BZLA_RELEASE_STACK(args);
          return 0;
        }
        BZLA_PUSH_STACK(args, sort);
      }
    } while (tag != BZLA_RPAR_TAG_SMT2);
  }

  /* parse return sort */
  tag         = read_token_smt2(parser);
  is_bool_var = tag == BZLA_BOOL_TAG_SMT2;
  if (!parse_sort(parser, tag, true, &sort))
  {
    BZLA_RELEASE_STACK(args);
    return 0;
  }
  /* bit-vector/array variable */
  if (BZLA_EMPTY_STACK(args))
  {
    if (bitwuzla_sort_is_fun(sort))
    {
      fun->exp = bitwuzla_mk_const(bitwuzla, sort, fun->name);
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
               2,
               "declared bit-vector array '%s' at line %d column %d",
               fun->name,
               fun->coo.x,
               fun->coo.y);
      parser->need_arrays = true;
    }
    else
    {
      fun->exp = bitwuzla_mk_const(bitwuzla, sort, fun->name);
      if (is_bool_var) bitwuzla_term_var_mark_bool(fun->exp);
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
               2,
               "declared '%s' as bit-vector at line %d column %d",
               fun->name,
               fun->coo.x,
               fun->coo.y);
    }
  }
  else
  {
    /* check if arguments have bit-vector sort, all other sorts are not
     * supported for uninterpreted functions */
    for (i = 0; i < BZLA_COUNT_STACK(args); i++)
    {
      const BitwuzlaSort *sort_arg = BZLA_PEEK_STACK(args, i);
      if (bitwuzla_sort_is_fun(sort_arg) || bitwuzla_sort_is_array(sort_arg))
      {
        BZLA_RELEASE_STACK(args);
        return !perr_smt2(parser,
                          "array and function sorts not supported "
                          "for arguments of uninterpreted functions");
      }
    }
    if (bitwuzla_sort_is_fun(sort) || bitwuzla_sort_is_array(sort))
    {
      BZLA_RELEASE_STACK(args);
      return !perr_smt2(parser,
                        "array and function sorts not supported as "
                        "return sort for uninterpreted functions");
    }

    s = bitwuzla_mk_fun_sort(
        bitwuzla, BZLA_COUNT_STACK(args), args.start, sort);
    fun->exp = bitwuzla_mk_const(bitwuzla, s, fun->name);
    BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
             2,
             "declared '%s' as uninterpreted function at line %d column %d",
             fun->name,
             fun->coo.x,
             fun->coo.y);
    parser->need_functions = true;
  }
  BZLA_RELEASE_STACK(args);
  return read_rpar_smt2(parser, " to close declaration");
}

/* Note: if we're currently parsing a model, define-fun for sorted vars
 *       have to be transformed into assertions of the form
 *       assert (= var assignment), define-funs for funs with args >= 1
 *       have to be built before asserting.
 *       Further, all symbols we parse are already defined -> check sort. */
static int32_t
define_fun_smt2(BzlaSMT2Parser *parser)
{
  int32_t tag, nargs = 0;
  const BitwuzlaTerm *eq, *tmp, *exp = 0;
  BzlaSMT2Coo coo;
  BzlaSMT2Item *item;
  BzlaSMT2Node *fun, *arg, *new_arg;
  BitwuzlaTermConstPtrStack args;
  const BitwuzlaSort *sort, *s;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  fun   = 0;
  arg   = 0;
  coo.x = coo.y = 0;

  if (!read_symbol(parser, " after 'define-fun'", &fun)) return 0;
  assert(fun && fun->tag == BZLA_SYMBOL_TAG_SMT2);

  if (fun->coo.x && !parser->commands.model)
  {
    return !perr_smt2(parser,
                      "symbol '%s' already defined at line %d column %d",
                      fun->name,
                      fun->coo.x,
                      fun->coo.y);
  }
  else if (!fun->coo.x && parser->commands.model)
  {
    return !perr_smt2(parser, "symbol '%s' undefined");
  }
  else /* do not redefine during model parsing */
  {
    fun->coo = parser->coo;
  }

  if (!read_lpar_smt2(parser, " after function name")) return 0;

  /* parse function arguments */
  do
  {
    tag = read_token_smt2(parser);

    if (tag != BZLA_RPAR_TAG_SMT2)
    {
      if (tag != BZLA_LPAR_TAG_SMT2) return !perr_smt2(parser, "expected '('");
      if (!read_symbol(parser, " after '('", &arg)) return 0;
      assert(arg && arg->tag == BZLA_SYMBOL_TAG_SMT2);

      if (arg->coo.x)
      {
        new_arg       = new_node_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
        new_arg->name = bzla_mem_strdup(parser->mem, arg->name);
        /* symbol may already be in symbol table */
        insert_symbol_smt2(parser, new_arg);
        arg = new_arg;
      }
      arg->coo = parser->coo;

      tag = read_token_smt2(parser);
      if (!parse_sort(parser, tag, false, &s)) return 0;
      nargs++;
      arg->exp   = bitwuzla_mk_var(bitwuzla, s, arg->name);
      item       = push_item_smt2(parser, arg->tag);
      item->node = arg;

      if (!read_rpar_smt2(parser, " after argument sort")) return 0;
    }
  } while (tag != BZLA_RPAR_TAG_SMT2);

  /* parse return sort */
  tag = read_token_smt2(parser);
  if (!parse_sort(parser, tag, true, &sort)) return 0;
  if (bitwuzla_sort_is_array(sort))
  {
    if (nargs)
    {
      return !perr_smt2(parser, "sort Array is not supported for arity > 0");
    }

    if (!parser->commands.model)
    {
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
               2,
               "defined bit-vector array '%s' at line %d column %d",
               fun->name,
               fun->coo.x,
               fun->coo.y);
      parser->need_arrays = true;
    }
    else
    {
      if (!bitwuzla_term_is_array(fun->exp))
        return !perr_smt2(parser, "sort Array expected");
      if (bitwuzla_term_get_sort(fun->exp) != sort)
        return !perr_smt2(parser, "array sort mismatch");
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
               2,
               "parsed bit-vector array '%s' at line %d column %d",
               fun->name,
               fun->coo.x,
               fun->coo.y);
      assert(parser->need_arrays);
    }
  }
  else
  {
    if (!parser->commands.model)
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
               2,
               "defined '%s' as bit-vector at line %d column %d",
               fun->name,
               fun->coo.x,
               fun->coo.y);
    else
    {
      if ((bitwuzla_term_is_fun(fun->exp)
           && bitwuzla_term_fun_get_codomain_sort(fun->exp) != sort)
          || (!bitwuzla_term_is_fun(fun->exp)
              && bitwuzla_term_get_sort(fun->exp) != sort))
      {
        return !perr_smt2(parser, "invalid sort, expected");
      }
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
               2,
               "parsed '%s' as bit-vector at line %d column %d",
               fun->name,
               fun->coo.x,
               fun->coo.y);
    }
  }

  if (!parse_term_smt2(parser, &exp, &coo)) return 0;

  // TODO (ma): this temporarily disables the sort check for function models
  //            until we have a api function for retrieving the index/element
  //            sorts of an array sort.
  if (!parser->commands.model && bitwuzla_term_get_sort(exp) != sort)
  {
    return !perr_smt2(parser, "invalid term sort");
  }

  if (nargs)
  {
    BZLA_INIT_STACK(parser->mem, args);
    item = parser->work.top - nargs;
    /* collect arguments, remove symbols (scope is only this function) */
    while (item < parser->work.top)
    {
      arg = item->node;
      item++;
      assert(arg);
      assert(arg->coo.x);
      assert(arg->tag == BZLA_SYMBOL_TAG_SMT2);
      BZLA_PUSH_STACK(args, arg->exp);
      remove_symbol_smt2(parser, arg);
    }
    BZLA_PUSH_STACK(args, exp);
    parser->work.top -= nargs;
    assert(BZLA_EMPTY_STACK(parser->work));
    tmp = bitwuzla_mk_term(
        bitwuzla, BITWUZLA_KIND_LAMBDA, BZLA_COUNT_STACK(args), args.start);
    if (parser->commands.model)
    {
      if (!bitwuzla_term_is_equal_sort(fun->exp, tmp))
      {
        BZLA_RELEASE_STACK(args);
        return !perr_smt2(parser, "model must have equal sort");
      }
      eq = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_EQUAL, fun->exp, tmp);
      bitwuzla_assert(bitwuzla, eq);
    }
    else
    {
      fun->exp = tmp;
      bitwuzla_term_set_symbol(fun->exp, fun->name);
      parser->need_functions = true;
    }
    BZLA_RELEASE_STACK(args);
  }
  else
  {
    if (parser->commands.model)
    {
      if (!bitwuzla_term_is_equal_sort(fun->exp, exp))
      {
        return !perr_smt2(parser, "model must have equal sort");
      }
      eq = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_EQUAL, fun->exp, exp);
      bitwuzla_assert(bitwuzla, eq);
    }
    else
    {
      fun->exp = exp;
      /* Only assign a symbol if the given term does not have a symbol yet. */
      if (!bitwuzla_term_get_symbol(fun->exp))
      {
        bitwuzla_term_set_symbol(fun->exp, fun->name);
      }
    }
  }
  return read_rpar_smt2(parser, " to close definition");
}

static int32_t
define_sort_smt2(BzlaSMT2Parser *parser)
{
  int32_t tag;
  BzlaSMT2Node *sort_alias;
  const BitwuzlaSort *sort;

  sort_alias = 0;
  if (!read_symbol(parser, " after 'define-sort'", &sort_alias)) return 0;
  assert(sort_alias);
  assert(sort_alias->tag == BZLA_SYMBOL_TAG_SMT2);

  if (sort_alias->coo.x)
  {
    return !perr_smt2(parser,
                      "sort '%s' already defined at line %d column %d",
                      sort_alias->name,
                      sort_alias->coo.x,
                      sort_alias->coo.y);
  }

  if (!read_lpar_smt2(parser, " after sort definition")) return 0;
  // TODO (ma): for now we do not support parameterized sort defintions
  if (!read_rpar_smt2(parser,
                      " parameterized sort definitions not supported yet"))
    return 0;

  tag = read_token_smt2(parser);
  if (!parse_sort(parser, tag, true, &sort)) return 0;

  sort_alias->sort       = 1;
  sort_alias->sort_alias = sort;
  return read_rpar_smt2(parser, " to close sort definition");
}

static int32_t
declare_sort_smt2(BzlaSMT2Parser *parser)
{
  uint32_t arity, opt_bit_width = 0;
  BzlaSMT2Node *sort_alias;
  const BitwuzlaSort *sort;

  opt_bit_width =
      bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_DECLSORT_BV_WIDTH);
  if (!opt_bit_width)
    return !perr_smt2(parser,
                      "'declare-sort' not supported if it is not interpreted"
                      " as a bit-vector, try --declsort-bv-width=<n>");

  sort_alias = 0;
  if (!read_symbol(parser, " after 'declare-sort'", &sort_alias)) return 0;
  assert(sort_alias);
  assert(sort_alias->tag == BZLA_SYMBOL_TAG_SMT2);

  if (sort_alias->coo.x)
  {
    return !perr_smt2(parser,
                      "sort '%s' already defined at line %d column %d",
                      sort_alias->name,
                      sort_alias->coo.x,
                      sort_alias->coo.y);
  }

  if (!parse_uint32_smt2(parser, true, &arity)) return 0;
  if (arity != 0)
    return !perr_smt2(parser, "sort arity other than 0 not supported");

  sort                   = bitwuzla_mk_bv_sort(parser->bitwuzla, opt_bit_width);
  sort_alias->sort       = 1;
  sort_alias->sort_alias = sort;
  BZLA_PUSH_STACK(parser->sorts, sort);
  return read_rpar_smt2(parser, " to close sort declaration");
}

static int32_t
echo_smt2(BzlaSMT2Parser *parser)
{
  int32_t tag;

  tag = read_token_smt2(parser);

  if (tag == BZLA_INVALID_TAG_SMT2) return 0;

  if (tag == EOF)
    return !perr_smt2(parser, "unexpected end-of-file after 'echo'");

  if (tag == BZLA_RPAR_TAG_SMT2)
    return !perr_smt2(parser, "string after 'echo' missing");

  if (tag != BZLA_STRING_CONSTANT_TAG_SMT2)
    return !perr_smt2(parser, "expected string after 'echo'");

  char *str = bzla_mem_strdup(parser->mem, parser->token.start);
  if (!read_rpar_smt2(parser, " after 'echo'"))
  {
    bzla_mem_freestr(parser->mem, str);
    return 0;
  }
  fprintf(parser->outfile, "%s\n", str);
  fflush(parser->outfile);
  bzla_mem_freestr(parser->mem, str);
  return 1;
}

static int32_t
set_info_smt2(BzlaSMT2Parser *parser)
{
  int32_t tag = read_token_smt2(parser);
  if (tag == BZLA_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2(parser, "unexpected end-of-file after 'set-info'");
  if (tag == BZLA_RPAR_TAG_SMT2)
    return !perr_smt2(parser, "keyword after 'set-info' missing");
  if (tag == BZLA_STATUS_TAG_SMT2)
  {
    tag = read_token_smt2(parser);
    if (tag == BZLA_INVALID_TAG_SMT2) return 0;
    if (tag == EOF)
      return !perr_smt2(parser, "unexpected end-of-file after ':status'");
    if (tag == BZLA_RPAR_TAG_SMT2)
      return !perr_smt2(parser, "value after ':status' missing");
    if (tag != BZLA_SYMBOL_TAG_SMT2)
    INVALID_STATUS_VALUE:
      return !perr_smt2(
          parser, "invalid value '%s' after ':status'", parser->token.start);
    if (!strcmp(parser->token.start, "sat"))
      parser->res->status = BITWUZLA_SAT;
    else if (!strcmp(parser->token.start, "unsat"))
      parser->res->status = BITWUZLA_UNSAT;
    else if (!strcmp(parser->token.start, "unknown"))
      parser->res->status = BITWUZLA_UNKNOWN;
    else
      goto INVALID_STATUS_VALUE;

    BZLA_MSG(bitwuzla_get_bzla_msg(parser->bitwuzla),
             2,
             "parsed status '%s'",
             parser->token.start);
    return read_rpar_smt2(parser, " after 'set-info'");
  }
  return skip_sexprs(parser, 1);
}

static int32_t
set_option_smt2(BzlaSMT2Parser *parser)
{
  int32_t tag, val, verb = 0;
  char *opt;
  BitwuzlaOption o;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  tag = read_token_smt2(parser);
  if (tag == BZLA_INVALID_TAG_SMT2) return 0;
  if (tag == EOF)
    return !perr_smt2(parser, "unexpected end-of-file after 'set-option'");
  if (tag == BZLA_RPAR_TAG_SMT2)
    return !perr_smt2(parser, "keyword after 'set-option' missing");

  /* parser specific options */
  if (tag == BZLA_PRODUCE_UNSAT_ASSUMPTIONS_TAG_SMT2)
  {
    /* do nothing, enabled by default */
  }
  else if (tag == BZLA_REGULAR_OUTPUT_CHANNEL_TAG_SMT2)
  {
    assert(parser->outfile != stdin);
    if (parser->outfile != stdout && parser->outfile != stderr)
      fclose(parser->outfile);
    tag = read_token_smt2(parser);
    if (tag == BZLA_INVALID_TAG_SMT2)
    {
      assert(parser->error);
      return 0;
    }
    parser->outfile = fopen(parser->token.start, "w");
    if (!parser->outfile)
      return !perr_smt2(parser, "can not create '%s'", parser->token.start);
  }
  else if (tag == BZLA_PRINT_SUCCESS_TAG_SMT2)
  {
    tag = read_token_smt2(parser);
    if (tag == BZLA_INVALID_TAG_SMT2)
    {
      assert(parser->error);
      return 0;
    }
    else if (tag == BZLA_TRUE_TAG_SMT2)
    {
      parser->print_success = true;
      configure_smt_comp_mode(parser);
    }
    else if (tag == BZLA_FALSE_TAG_SMT2)
      parser->print_success = false;
    else
      return !perr_smt2(
          parser, "expected Boolean argument at '%s'", parser->token.start);
  }
  else if (tag == BZLA_GLOBAL_DECLARATIONS_TAG_SMT2)
  {
    tag = read_token_smt2(parser);
    if (tag == BZLA_INVALID_TAG_SMT2)
    {
      assert(parser->error);
      return 0;
    }
    if (tag == BZLA_FALSE_TAG_SMT2)
      parser->global_declarations = false;
    else if (tag == BZLA_TRUE_TAG_SMT2)
      parser->global_declarations = true;
    else
      return !perr_smt2(
          parser, "expected Boolean argument at '%s'", parser->token.start);
  }
  /* Bitwuzla specific options */
  else
  {
    if (tag == BZLA_PRODUCE_MODELS_TAG_SMT2)
    {
      o = BITWUZLA_OPT_PRODUCE_MODELS;
    }
    else if (tag == BZLA_PRODUCE_UNSAT_CORES_TAG_SMT2)
    {
      o = BITWUZLA_OPT_PRODUCE_UNSAT_CORES;
    }
    else
    {
      opt = parser->token.start + 1;
      o   = bitwuzla_get_option_from_string(bitwuzla, opt);
      if (o == BITWUZLA_OPT_NUM_OPTS)
      {
        return !perr_smt2(parser, "unsupported option: '%s'", opt);
      }
    }

    tag = read_token_smt2(parser);
    if (tag == BZLA_INVALID_TAG_SMT2)
    {
      assert(parser->error);
      return 0;
    }
    val = bitwuzla_get_option(bitwuzla, o);
    if (tag == BZLA_FALSE_TAG_SMT2)
      val = 0;
    else if (tag == BZLA_TRUE_TAG_SMT2)
      val = 1;
    else
      val = verb ? val + atoi(parser->token.start) : atoi(parser->token.start);
    bitwuzla_set_option(bitwuzla, o, val);
  }
  return skip_sexprs(parser, 1);
}

static void
print_success(BzlaSMT2Parser *parser)
{
  if (!parser->print_success) return;
  fprintf(parser->outfile, "success\n");
  fflush(parser->outfile);
}

static void
check_sat(BzlaSMT2Parser *parser)
{
  assert(!parser->error);
  Bitwuzla *bitwuzla = parser->bitwuzla;
  BZLA_RESET_STACK(parser->sat_assuming_assumptions);
  if (parser->commands.check_sat++
      && !bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_INCREMENTAL))
  {
    BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
             1,
             "WARNING additional 'check-sat' command");
  }
  if (bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_PARSE_INTERACTIVE))
  {
    BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
             1,
             "parsed %d commands in %.2f seconds",
             parser->commands.all,
             bzla_util_time_stamp() - parser->parse_start);
    parser->res->result = bitwuzla_check_sat(bitwuzla);
    parser->res->nsatcalls += 1;
    if (parser->res->result == BITWUZLA_SAT)
    {
      fprintf(parser->outfile, "sat\n");
    }
    else if (parser->res->result == BITWUZLA_UNSAT)
    {
      fprintf(parser->outfile, "unsat\n");
    }
    /* Do not print 'unknown' if we print DIMACS. 'unknown' is only returned if
     * SAT solver is used non-incremental. */
    else if (!bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_PRINT_DIMACS))
    {
      fprintf(parser->outfile, "unknown\n");
    }
    fflush(parser->outfile);
  }
  else
  {
    BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
             1,
             "parser not interactive, aborted on first "
             "'check-sat' command");
    parser->done = true;
  }
}

static int32_t
read_exp_list(BzlaSMT2Parser *parser,
              BitwuzlaTermConstPtrStack *exps,
              BzlaSMT2Coo *coo)
{
  int32_t tag             = 0;
  const BitwuzlaTerm *exp = 0;

  /* parse list of symbols/terms */
  BZLA_INIT_STACK(parser->mem, *exps);
  parser->store_tokens = true;
  if (!parse_term_aux_smt2(parser, false, 0, &exp, coo))
  {
    BZLA_RELEASE_STACK(*exps);
    return 0;
  }
  if (BZLA_TOP_STACK(parser->tokens) == ' ')
    (void) BZLA_POP_STACK(parser->tokens);
  BZLA_PUSH_STACK(parser->tokens, 0);
  BZLA_PUSH_STACK(*exps, exp);
  tag = read_token_smt2(parser);
  while (tag != EOF && tag != BZLA_RPAR_TAG_SMT2)
  {
    if (!parse_term_aux_smt2(parser, true, tag, &exp, coo))
    {
      BZLA_RELEASE_STACK(*exps);
      return 0;
    }
    if (BZLA_TOP_STACK(parser->tokens) == ' ')
      (void) BZLA_POP_STACK(parser->tokens);
    BZLA_PUSH_STACK(parser->tokens, 0);
    BZLA_PUSH_STACK(*exps, exp);
    tag = read_token_smt2(parser);
  }
  parser->store_tokens = false;
  return 1;
}

static int32_t
read_command_smt2(BzlaSMT2Parser *parser)
{
  uint32_t i, width, level;
  int32_t tag;
  const BitwuzlaTerm *exp = 0;
  BzlaSMT2Coo coo;
  BzlaSMT2Node *logic = 0;
  BitwuzlaTermConstPtrStack exps;
  const BitwuzlaTerm **failed_assumptions, **unsat_core;
  Bitwuzla *bitwuzla = parser->bitwuzla;

  coo.x = coo.y = 0;
  tag           = read_token_smt2(parser);

  if (parser->commands.model && tag == BZLA_RPAR_TAG_SMT2)
  {
    parser->commands.model = 0;
    return 0;
  }
  if (parser->commands.model && tag == EOF)
    return !perr_smt2(parser, "expected ')' after 'model' at end-of-file");

  if (tag == EOF || tag == BZLA_INVALID_TAG_SMT2) return 0;
  if (tag != BZLA_LPAR_TAG_SMT2)
    return !perr_smt2(parser, "expected '(' at '%s'", parser->token.start);
  tag = read_token_smt2(parser);

  if (tag == EOF)
  {
    parser->perrcoo = parser->lastcoo;
    return !perr_smt2(parser, "unexpected end-of-file after '('");
  }

  if (tag == BZLA_INVALID_TAG_SMT2)
  {
    assert(parser->error);
    return 0;
  }

  if (parser->commands.model && tag != BZLA_DEFINE_FUN_TAG_SMT2)
    return !perr_smt2(parser, "expected 'define-fun' after 'model'");

  if (!(tag & BZLA_COMMAND_TAG_CLASS_SMT2))
    return !perr_smt2(parser, "expected command at '%s'", parser->token.start);

  if (parser->commands.model && tag != BZLA_DEFINE_FUN_TAG_SMT2)
    return !perr_smt2(parser, "'define-fun' command expected");

  switch (tag)
  {
    case BZLA_SET_LOGIC_TAG_SMT2:
      if (!read_symbol(parser, " after set-logic", &logic))
      {
        return 0;
      }
      if (tag == EOF)
      {
        parser->perrcoo = parser->lastcoo;
        return !perr_smt2(parser, "unexpected end-of-file after 'set-logic'");
      }
      if (tag == BZLA_INVALID_TAG_SMT2)
      {
        assert(parser->error);
        return 0;
      }
      assert(logic);
      if (is_supported_logic(logic->name))
      {
        parser->logic = bzla_mem_strdup(parser->mem, logic->name);
      }
      else
      {
        return !perr_smt2(parser, "unsupported logic '%s'", logic->name);
      }
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla), 2, "logic %s", logic->name);
      if (!read_rpar_smt2(parser, " after logic")) return 0;
      if (parser->commands.set_logic++)
        BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
                 1,
                 "WARNING additional 'set-logic' command");
      print_success(parser);
      break;

    case BZLA_CHECK_SAT_TAG_SMT2:
      configure_smt_comp_mode(parser);
      if (!read_rpar_smt2(parser, " after 'check-sat'")) return 0;
      check_sat(parser);
      break;

    case BZLA_CHECK_SAT_ASSUMING_TAG_SMT2:
      configure_smt_comp_mode(parser);
      if (!read_lpar_smt2(parser, " after 'check-sat-assuming'")) return 0;
      if (!bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_INCREMENTAL))
        return !perr_smt2(parser, "incremental solving is not enabled");
      if (!read_exp_list(parser, &exps, &coo))
      {
        BZLA_RELEASE_STACK(exps);
        return 0;
      }
      for (i = 0; i < BZLA_COUNT_STACK(exps); i++)
      {
        exp = BZLA_PEEK_STACK(exps, i);
        if (bitwuzla_term_is_array(exp))
        {
          parser->perrcoo = coo;
          BZLA_RELEASE_STACK(exps);
          return !perr_smt2(
              parser, "assumption argument is an array and not a formula");
        }
        bitwuzla_assume(parser->bitwuzla, exp);
      }
      if (!read_rpar_smt2(parser, " after 'check-sat-assuming'"))
      {
        BZLA_RELEASE_STACK(exps);
        return 0;
      }
      check_sat(parser);
      for (i = 0; i < BZLA_COUNT_STACK(exps); i++)
      {
        exp = BZLA_PEEK_STACK(exps, i);
        BZLA_PUSH_STACK(parser->sat_assuming_assumptions, exp);
      }
      BZLA_RELEASE_STACK(exps);
      BZLA_RESET_STACK(parser->tokens);
      break;

    case BZLA_DECLARE_FUN_TAG_SMT2:
      if (!declare_fun_smt2(parser, false)) return 0;
      print_success(parser);
      break;

    case BZLA_DECLARE_CONST_TAG_SMT2:
      if (!declare_fun_smt2(parser, true)) return 0;
      print_success(parser);
      break;

    case BZLA_DEFINE_FUN_TAG_SMT2:
      if (!define_fun_smt2(parser)) return 0;
      print_success(parser);
      break;

    case BZLA_DECLARE_SORT_TAG_SMT2:
      configure_smt_comp_mode(parser);
      if (!declare_sort_smt2(parser)) return 0;
      print_success(parser);
      break;

    case BZLA_DEFINE_SORT_TAG_SMT2:
      if (!define_sort_smt2(parser)) return 0;
      print_success(parser);
      break;

    case BZLA_ASSERT_TAG_SMT2:
      if (!parse_term_smt2(parser, &exp, &coo)) return 0;
      assert(!parser->error);
      if (!bitwuzla_term_is_bv(exp)
          || bitwuzla_sort_bv_get_size(bitwuzla_term_get_sort(exp)) != 1)
      {
        parser->perrcoo = coo;
        return !perr_smt2(parser, "assert argument is not a formula");
      }
      if (!read_rpar_smt2(parser, " after asserted expression"))
      {
        return 0;
      }
      if ((width = bitwuzla_term_bv_get_size(exp)) != 1)
      {
        parser->perrcoo = coo;
        return !perr_smt2(
            parser, "assert argument is a bit-vector of length %d", width);
      }
      bitwuzla_assert(bitwuzla, exp);
      assert(!parser->error);
      parser->commands.asserts++;
      print_success(parser);
      break;

    case BZLA_ECHO_TAG_SMT2:
      if (!echo_smt2(parser)) return 0;
      break;

    case BZLA_EXIT_TAG_SMT2:
      if (!read_rpar_smt2(parser, " after 'exit'")) return 0;
      assert(!parser->commands.exits);
      parser->commands.exits++;
      parser->done = true;
      print_success(parser);
      break;

    case BZLA_GET_MODEL_TAG_SMT2:
      if (!read_rpar_smt2(parser, " after 'get-model'")) return 0;
      if (!bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS))
        return !perr_smt2(parser, "model generation is not enabled");
      if (parser->res->result != BITWUZLA_SAT) break;
      if (bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_OUTPUT_FORMAT)
          == BZLA_OUTPUT_FORMAT_BTOR)
      {
        bitwuzla_print_model(bitwuzla, "btor", parser->outfile);
      }
      else
      {
        bitwuzla_print_model(bitwuzla, "smt2", parser->outfile);
      }
      fflush(parser->outfile);
      break;

    case BZLA_GET_UNSAT_ASSUMPTIONS_TAG_SMT2: {
      if (!read_rpar_smt2(parser, " after 'get-unsat-assumptions'")) return 0;
      if (parser->res->result != BITWUZLA_UNSAT) break;
      fputc('(', parser->outfile);
      size_t size;
      failed_assumptions = bitwuzla_get_unsat_assumptions(bitwuzla, &size);
      for (i = 0; i < size; ++i)
      {
        if (i > 0) fputc(' ', parser->outfile);
        const char *symbol = bitwuzla_term_get_symbol(failed_assumptions[i]);
        if (symbol)
        {
          fprintf(parser->outfile, "%s", symbol);
        }
        else
        {
          bitwuzla_term_dump(failed_assumptions[i], "smt2", parser->outfile);
        }
      }
      failed_assumptions = 0;
      fputs(")\n", parser->outfile);
      fflush(parser->outfile);
      break;
    }

    case BZLA_GET_UNSAT_CORE_TAG_SMT2: {
      if (!read_rpar_smt2(parser, " after 'get-unsat-assumptions'")) return 0;
      if (parser->res->result != BITWUZLA_UNSAT) break;
      fputc('(', parser->outfile);
      size_t size;
      unsat_core = bitwuzla_get_unsat_core(bitwuzla, &size);
      const char *sym;
      bool printed_first = false;
      for (i = 0; i < size; ++i)
      {
        sym = bitwuzla_term_get_symbol(unsat_core[i]);
        if (!sym) continue;
        if (printed_first)
        {
          fputc(' ', parser->outfile);
        }
        fprintf(parser->outfile, "%s", sym);
        printed_first = true;
      }
      unsat_core = 0;
      fputs(")\n", parser->outfile);
      fflush(parser->outfile);
      break;
    }

    case BZLA_GET_VALUE_TAG_SMT2:
      if (!read_lpar_smt2(parser, " after 'get-value'")) return 0;
      if (!bitwuzla_get_option(parser->bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS))
      {
        return !perr_smt2(parser, "model generation is not enabled");
      }
      if (parser->res->result != BITWUZLA_SAT) break;
      if (!read_exp_list(parser, &exps, &coo))
      {
        BZLA_RELEASE_STACK(exps);
        return 0;
      }
      if (!read_rpar_smt2(parser, " after 'get-value'"))
      {
        BZLA_RELEASE_STACK(exps);
        return 0;
      }
      fputc('(', parser->outfile);
      char *symbols = parser->tokens.start;
      for (i = 0; i < BZLA_COUNT_STACK(exps); i++)
      {
        if (BZLA_COUNT_STACK(exps) > 1) fputs("\n ", parser->outfile);
        exp = BZLA_PEEK_STACK(exps, i);
        bitwuzla_term_print_value_smt2(exp, symbols, parser->outfile);
        symbols += strlen(symbols) + 1;
        assert(symbols <= parser->tokens.top);
      }
      if (BZLA_COUNT_STACK(exps) > 1) fputc('\n', parser->outfile);
      fprintf(parser->outfile, ")\n");
      fflush(parser->outfile);
      BZLA_RELEASE_STACK(exps);
      BZLA_RESET_STACK(parser->tokens);
      break;

    case BZLA_MODEL_TAG_SMT2:
      // FIXME model parsing for arrays currently disabled
      if (parser->need_arrays)
        return !perr_smt2(parser,
                          "model parsing for arrays currently not supported");
      ///////////
      if (parser->commands.model)
        return !perr_smt2(parser, "nesting models is invalid");
      parser->commands.model = 1;
      while (read_command_smt2(parser) && !bitwuzla_terminate(bitwuzla))
        ;
      break;

    case BZLA_SET_INFO_TAG_SMT2:
      if (!set_info_smt2(parser)) return 0;
      print_success(parser);
      break;

    case BZLA_SET_OPTION_TAG_SMT2:
      if (!set_option_smt2(parser)) return 0;
      print_success(parser);
      break;

    case BZLA_PUSH_TAG_SMT2:
      level = 0;
      (void) parse_uint32_smt2(parser, true, &level);
      if (!read_rpar_smt2(parser, " after 'push'")) return 0;
      for (i = 0; i < level; i++) open_new_scope(parser);
      configure_smt_comp_mode(parser);
      bitwuzla_push(bitwuzla, level);
      print_success(parser);
      break;

    case BZLA_POP_TAG_SMT2:
      (void) parse_uint32_smt2(parser, true, &level);
      if (!read_rpar_smt2(parser, " after 'pop'")) return 0;
      if (level > parser->scope_level)
      {
        return !perr_smt2(parser,
                          "popping more scopes (%u) than created via push (%u)",
                          level,
                          parser->scope_level);
      }
      for (i = 0; i < level; i++) close_current_scope(parser);
      bitwuzla_pop(bitwuzla, level);
      print_success(parser);
      break;

    default:
      return !perr_smt2(
          parser, "unsupported command '%s'", parser->token.start);
      break;
  }
  parser->commands.all++;
  return 1;
}

static const char *
parse_smt2_parser(BzlaSMT2Parser *parser,
                  BzlaIntStack *prefix,
                  FILE *infile,
                  const char *infile_name,
                  FILE *outfile,
                  BzlaParseResult *res)
{
  double start = bzla_util_time_stamp(), delta;

  parser->nprefix     = 0;
  parser->prefix      = prefix;
  parser->nextcoo.x   = 1;
  parser->nextcoo.y   = 1;
  parser->infile      = infile;
  parser->infile_name = bzla_mem_strdup(parser->mem, infile_name);
  parser->outfile     = outfile;
  parser->saved       = false;
  parser->parse_start = start;
  BZLA_CLR(res);
  parser->res   = res;
  parser->logic = 0;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  while (read_command_smt2(parser) && !parser->done
         && !bitwuzla_terminate(bitwuzla))
    ;

  if (parser->error) return parser->error;

  if (!bitwuzla_terminate(bitwuzla))
  {
    if (!parser->commands.all)
    {
      BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
               1,
               "WARNING no commands in '%s'",
               parser->infile_name);
    }
    else
    {
      if (!parser->commands.set_logic)
        BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
                 1,
                 "WARNING 'set-logic' command missing in '%s'",
                 parser->infile_name);
      if (!parser->commands.asserts)
        BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
                 1,
                 "WARNING no 'assert' command in '%s'",
                 parser->infile_name);
      if (!parser->commands.check_sat)
        BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
                 1,
                 "WARNING 'check-sat' command missing in '%s'",
                 parser->infile_name);
      if (!parser->commands.exits)
        BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
                 1,
                 "WARNING no 'exit' command at end of '%s'",
                 parser->infile_name);
    }
  }
  delta = bzla_util_time_stamp() - start;
  if (delta < 0) delta = 0;
  BZLA_MSG(bitwuzla_get_bzla_msg(bitwuzla),
           1,
           "parsed %d commands in %.2f seconds",
           parser->commands.all,
           delta);
  return 0;
}

static BzlaParserAPI parsesmt2_parser_api = {
    (BzlaInitParser) new_smt2_parser,
    (BzlaResetParser) delete_smt2_parser,
    (BzlaParse) parse_smt2_parser};

const BzlaParserAPI *
bzla_parsesmt2_parser_api()
{
  return &parsesmt2_parser_api;
}
