/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *  Copyright (C) 2012-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLADBG_H_INCLUDED
#define BZLADBG_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "bzlacore.h"

/*------------------------------------------------------------------------*/
/* core                                                                   */
/*------------------------------------------------------------------------*/

bool bzla_dbg_check_lambdas_static_rho_proxy_free(const Bzla* bzla);

bool bzla_dbg_check_unique_table_children_proxy_free(const Bzla* bzla);

bool bzla_dbg_check_unique_table_rebuild(const Bzla* bzla);

bool bzla_dbg_check_hash_table_proxy_free(BzlaPtrHashTable* table);

bool bzla_dbg_check_all_hash_tables_proxy_free(const Bzla* bzla);

bool bzla_dbg_check_hash_table_simp_free(BzlaPtrHashTable* table);

bool bzla_dbg_check_all_hash_tables_simp_free(const Bzla* bzla);

bool bzla_dbg_check_constraints_not_const(const Bzla* bzla);

bool bzla_dbg_check_assumptions_simp_free(const Bzla* bzla);

bool bzla_dbg_check_constraints_simp_free(Bzla* bzla);

bool bzla_dbg_check_nodes_simp_free(Bzla* bzla,
                                    BzlaNode* nodes[],
                                    size_t nnodes);

/*------------------------------------------------------------------------*/
/* exp                                                                    */
/*------------------------------------------------------------------------*/

bool bzla_dbg_precond_slice_exp(Bzla* bzla,
                                const BzlaNode* exp,
                                uint32_t upper,
                                uint32_t lower);

bool bzla_dbg_precond_ext_exp(Bzla* bzla, const BzlaNode* exp);

bool bzla_dbg_precond_regular_unary_bv_exp(Bzla* bzla, const BzlaNode* exp);

bool bzla_dbg_precond_regular_binary_bv_exp(Bzla* bzla,
                                            const BzlaNode* e0,
                                            const BzlaNode* e1);

/* Check assertions for unary fp expressions. */
bool bzla_dbg_precond_regular_unary_fp_exp(Bzla* bzla, const BzlaNode* exp);

/* Check assertions for binary fp expressions without rounding mode operand. */
bool bzla_dbg_precond_regular_binary_fp_exp(Bzla* bzla,
                                            const BzlaNode* e0,
                                            const BzlaNode* e1);

bool bzla_dbg_precond_eq_exp(Bzla* bzla,
                             const BzlaNode* e0,
                             const BzlaNode* e1);

bool bzla_dbg_precond_shift_exp(Bzla* bzla,
                                const BzlaNode* e0,
                                const BzlaNode* e1);

bool bzla_dbg_precond_concat_exp(Bzla* bzla,
                                 const BzlaNode* e0,
                                 const BzlaNode* e1);

bool bzla_dbg_precond_read_exp(Bzla* bzla,
                               const BzlaNode* e_array,
                               const BzlaNode* e_index);

bool bzla_dbg_precond_write_exp(Bzla* bzla,
                                const BzlaNode* e_array,
                                const BzlaNode* e_index,
                                const BzlaNode* e_value);

bool bzla_dbg_precond_cond_exp(Bzla* bzla,
                               const BzlaNode* e_cond,
                               const BzlaNode* e_if,
                               const BzlaNode* e_else);

bool bzla_dbg_precond_apply_exp(Bzla* bzla,
                                const BzlaNode* fun,
                                const BzlaNode* args);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
