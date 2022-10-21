#ifndef BZLA_REWRITE_REWRITES_BOOL_H_INCLUDED
#define BZLA_REWRITE_REWRITES_BOOL_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

/* and ---------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::AND_EVAL>::_apply(Rewriter& rewriter,
                                                    const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::AND_SPECIAL_CONST>::_apply(Rewriter& rewriter,
                                                             const Node& node);
// const1_and
template <>
Node RewriteRule<RewriteRuleKind::AND_CONST>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// idem1_and
template <>
Node RewriteRule<RewriteRuleKind::AND_IDEM1>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// idem2_and
template <>
Node RewriteRule<RewriteRuleKind::AND_IDEM2>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// idem3_and
template <>
Node RewriteRule<RewriteRuleKind::AND_IDEM3>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// contr1_and
template <>
Node RewriteRule<RewriteRuleKind::AND_CONTRA1>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// contr2_and
template <>
Node RewriteRule<RewriteRuleKind::AND_CONTRA2>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// contr3_and
template <>
Node RewriteRule<RewriteRuleKind::AND_CONTRA3>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// resol1_and
// resol2_and
template <>
Node RewriteRule<RewriteRuleKind::AND_RESOL1>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// subsum1_and
template <>
Node RewriteRule<RewriteRuleKind::AND_SUBSUM1>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// subsum2_and
template <>
Node RewriteRule<RewriteRuleKind::AND_SUBSUM2>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// subst1_and
// subst2_and
template <>
Node RewriteRule<RewriteRuleKind::AND_NOT_AND1>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// subst3_and
// subst4_and
template <>
Node RewriteRule<RewriteRuleKind::AND_NOT_AND2>::_apply(Rewriter& rewriter,
                                                        const Node& node);
// lt_false_and
template <>
Node RewriteRule<RewriteRuleKind::AND_BV_LT_FALSE>::_apply(Rewriter& rewriter,
                                                           const Node& node);
// lt_and
template <>
Node RewriteRule<RewriteRuleKind::AND_BV_LT>::_apply(Rewriter& rewriter,
                                                     const Node& node);

/* equal -------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::EQUAL_EVAL>::_apply(Rewriter& rewriter,
                                                      const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_SPECIAL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);
// true_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_TRUE>::_apply(Rewriter& rewriter,
                                                      const Node& node);
// false_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_FALSE>::_apply(Rewriter& rewriter,
                                                       const Node& node);
// bcond_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// bcond_if_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE_BV1>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// bcond_uneq_if_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ITE_DIS_BV1>::_apply(Rewriter& rewriter,
                                                             const Node& node);
// add_left_eq
// add_right_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ADD>::_apply(Rewriter& rewriter,
                                                     const Node& node);
// add_add_1_eq
// add_add_2_eq
// add_add_3_eq
// add_add_4_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_ADD_ADD>::_apply(Rewriter& rewriter,
                                                         const Node& node);
// concat_eq
template <>
Node RewriteRule<RewriteRuleKind::EQUAL_CONCAT>::_apply(Rewriter& rewriter,
                                                        const Node& node);

/* distinct ----------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::DISTINCT_CARD>::_apply(Rewriter& rewriter,
                                                         const Node& node);

/* not ---------------------------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::NOT_EVAL>::_apply(Rewriter& rewriter,
                                                    const Node& node);
// bool_xnor_and
template <>
Node RewriteRule<RewriteRuleKind::NOT_XOR>::_apply(Rewriter& rewriter,
                                                   const Node& node);

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node RewriteRule<RewriteRuleKind::DISTINCT_ELIM>::_apply(Rewriter& rewriter,
                                                         const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::IMPLIES_ELIM>::_apply(Rewriter& rewriter,
                                                        const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::OR_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::XOR_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node);

/* -------------------------------------------------------------------------- */
}  // namespace bzla

#endif
