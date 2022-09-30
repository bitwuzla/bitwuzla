#include "rewrite/rewriter.h"

#include "node/node_manager.h"
#include "rewrite/rewrites_bool.h"
#include "rewrite/rewrites_bv.h"
#include "rewrite/rewrites_fp.h"

#define BZLA_APPLY_RW_RULE(rw_rule)                                \
  do                                                               \
  {                                                                \
    std::tie(res, kind) =                                          \
        RewriteRule<RewriteRuleKind::rw_rule>::apply(*this, node); \
    if (res != node) goto DONE;                                    \
  } while (false);

#define BZLA_ELIM_KIND_IMPL(name, rule)           \
  Node Rewriter::rewrite_##name(const Node& node) \
  {                                               \
    RewriteRuleKind kind;                         \
    Node res;                                     \
                                                  \
    BZLA_APPLY_RW_RULE(rule);                     \
                                                  \
  DONE:                                           \
    return res;                                   \
  }

namespace bzla {

/* === Rewriter public ====================================================== */

const Node&
Rewriter::rewrite(const Node& node)
{
  NodeManager& nm = NodeManager::get();
  std::vector<std::reference_wrapper<const Node>> visit{node};
  do
  {
    const Node& cur = visit.back();
    auto [it, inserted] = d_cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.num_children())
      {
        std::vector<Node> children;
        std::vector<uint64_t> indices;
        for (const auto& c : cur)
        {
          children.push_back(d_cache.at(c));
          assert(!children.back().is_null());
        }
        for (size_t i = 0, n = cur.num_indices(); i < n; ++i)
        {
          indices.push_back(cur.index(i));
        }
        it->second = _rewrite(nm.mk_node(cur.kind(), children, indices));
      }
      else
      {
        it->second = cur;
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  assert(d_cache.find(node) != d_cache.end());
  return d_cache.at(node);
}

const Node&
Rewriter::mk_node(node::Kind kind,
                  const std::vector<Node>& children,
                  const std::vector<uint64_t>& indices)
{
  return _rewrite(NodeManager::get().mk_node(kind, children, indices));
}

/* === Rewriter private ===================================================== */

const Node&
Rewriter::_rewrite(const Node& node)
{
  // Lookup rewrite cache
  auto [it, inserted] = d_cache.emplace(node, Node());
  if (!inserted && !it->second.is_null())
  {
    return it->second;
  }

  Node res;
  switch (node.kind())
  {
    case node::Kind::AND: res = rewrite_and(node); break;
    case node::Kind::DISTINCT: res = rewrite_distinct(node); break;
    case node::Kind::NOT: res = rewrite_not(node); break;
    case node::Kind::OR: res = rewrite_or(node); break;

    case node::Kind::EQUAL: res = rewrite_eq(node); break;
    case node::Kind::ITE: res = rewrite_ite(node); break;

    case node::Kind::BV_AND: res = rewrite_bv_and(node); break;
    case node::Kind::BV_ADD: res = rewrite_bv_add(node); break;
    case node::Kind::BV_ASHR: res = rewrite_bv_ashr(node); break;
    case node::Kind::BV_CONCAT: res = rewrite_bv_concat(node); break;
    case node::Kind::BV_EXTRACT: res = rewrite_bv_extract(node); break;
    case node::Kind::BV_MUL: res = rewrite_bv_mul(node); break;
    case node::Kind::BV_NOT: res = rewrite_bv_not(node); break;
    case node::Kind::BV_SHL: res = rewrite_bv_shl(node); break;
    case node::Kind::BV_SHR: res = rewrite_bv_shr(node); break;
    case node::Kind::BV_SLT: res = rewrite_bv_slt(node); break;
    case node::Kind::BV_UDIV: res = rewrite_bv_udiv(node); break;
    case node::Kind::BV_ULT: res = rewrite_bv_ult(node); break;
    case node::Kind::BV_UREM: res = rewrite_bv_urem(node); break;
    case node::Kind::BV_COMP:
      res = node; // TODO
      break;

    /* Eliminated bit-vector operators */
    case node::Kind::BV_NAND: res = rewrite_bv_nand(node); break;
    case node::Kind::BV_NEG: res = rewrite_bv_neg(node); break;
    case node::Kind::BV_NOR: res = rewrite_bv_nor(node); break;
    case node::Kind::BV_OR: res = rewrite_bv_or(node); break;
    case node::Kind::BV_REDAND: res = rewrite_bv_redand(node); break;
    case node::Kind::BV_REDOR: res = rewrite_bv_redor(node); break;
    case node::Kind::BV_REDXOR: res = rewrite_bv_redxor(node); break;
    case node::Kind::BV_REPEAT: res = rewrite_bv_repeat(node); break;
    case node::Kind::BV_ROL: res = rewrite_bv_rol(node); break;
    case node::Kind::BV_ROLI: res = rewrite_bv_roli(node); break;
    case node::Kind::BV_ROR: res = rewrite_bv_ror(node); break;
    case node::Kind::BV_RORI: res = rewrite_bv_rori(node); break;
    case node::Kind::BV_SADDO: res = rewrite_bv_saddo(node); break;
    case node::Kind::BV_SDIV: res = rewrite_bv_sdiv(node); break;
    case node::Kind::BV_SDIVO: res = rewrite_bv_sdivo(node); break;
    case node::Kind::BV_SGE: res = rewrite_bv_sge(node); break;
    case node::Kind::BV_SGT: res = rewrite_bv_sgt(node); break;
    case node::Kind::BV_SIGN_EXTEND: res = rewrite_bv_sign_extend(node); break;
    case node::Kind::BV_SLE: res = rewrite_bv_sle(node); break;
    case node::Kind::BV_SMOD: res = rewrite_bv_smod(node); break;
    // case node::Kind::BV_SMULO: res = rewrite_bv_smulo(node); break;
    case node::Kind::BV_SREM: res = rewrite_bv_srem(node); break;
    case node::Kind::BV_SSUBO: res = rewrite_bv_ssubo(node); break;
    case node::Kind::BV_SUB: res = rewrite_bv_sub(node); break;
    // case node::Kind::BV_UMULO: res = rewrite_bv_umulo(node); break;
    case node::Kind::BV_UADDO: res = rewrite_bv_uaddo(node); break;
    case node::Kind::BV_UGE: res = rewrite_bv_uge(node); break;
    case node::Kind::BV_UGT: res = rewrite_bv_ugt(node); break;
    case node::Kind::BV_ULE: res = rewrite_bv_ule(node); break;
    case node::Kind::BV_USUBO: res = rewrite_bv_usubo(node); break;
    case node::Kind::BV_XNOR: res = rewrite_bv_xnor(node); break;
    case node::Kind::BV_XOR: res = rewrite_bv_xor(node); break;
    case node::Kind::BV_ZERO_EXTEND: res = rewrite_bv_zero_extend(node); break;

    case node::Kind::FP_ABS: res = rewrite_fp_abs(node); break;
    case node::Kind::FP_ADD: res = rewrite_fp_add(node); break;
    case node::Kind::FP_DIV: res = rewrite_fp_div(node); break;

    case node::Kind::FP_IS_INF: res = rewrite_fp_is_inf(node); break;
    case node::Kind::FP_IS_NAN: res = rewrite_fp_is_nan(node); break;
    case node::Kind::FP_IS_NEG: res = rewrite_fp_is_neg(node); break;
    case node::Kind::FP_IS_NORM: res = rewrite_fp_is_normal(node); break;
    case node::Kind::FP_IS_POS: res = rewrite_fp_is_pos(node); break;
    case node::Kind::FP_IS_SUBNORM: res = rewrite_fp_is_subnormal(node); break;
    case node::Kind::FP_IS_ZERO: res = rewrite_fp_is_zero(node); break;

    case node::Kind::FP_LE: res = rewrite_fp_le(node); break;
    case node::Kind::FP_LT: res = rewrite_fp_lt(node); break;
    case node::Kind::FP_MAX: res = rewrite_fp_max(node); break;
    case node::Kind::FP_MIN: res = rewrite_fp_min(node); break;
    case node::Kind::FP_MUL: res = rewrite_fp_mul(node); break;
    case node::Kind::FP_NEG: res = rewrite_fp_neg(node); break;
    case node::Kind::FP_REM: res = rewrite_fp_rem(node); break;
    case node::Kind::FP_RTI: res = rewrite_fp_rti(node); break;
    case node::Kind::FP_SQRT: res = rewrite_fp_sqrt(node); break;

    case node::Kind::FP_TO_FP_FROM_BV:
      res = rewrite_fp_to_fp_from_bv(node);
      break;
    case node::Kind::FP_TO_FP_FROM_FP:
      res = rewrite_fp_to_fp_from_fp(node);
      break;
    case node::Kind::FP_TO_FP_FROM_SBV:
      res = rewrite_fp_to_fp_from_sbv(node);
      break;
    case node::Kind::FP_TO_FP_FROM_UBV:
      res = rewrite_fp_to_fp_from_ubv(node);
      break;

    case node::Kind::APPLY: res = rewrite_apply(node); break;
    case node::Kind::LAMBDA: res = rewrite_lambda(node); break;

    case node::Kind::FORALL: res = rewrite_forall(node); break;
    case node::Kind::EXISTS: res = rewrite_exists(node); break;

    default: assert(false);
  }
  assert(res.type() == node.type());
  assert(it->second.is_null());

  // Cache result
  it->second = res;

  return it->second;
}

/* Boolean rewrites --------------------------------------------------------- */

Node
Rewriter::rewrite_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(AND_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_not(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(NOT_EVAL);
  // TODO

DONE:
  return res;
}

BZLA_ELIM_KIND_IMPL(distinct, DISTINCT_ELIM)
BZLA_ELIM_KIND_IMPL(or, OR_ELIM)

/* -------------------------------------------------------------------------- */

Node
Rewriter::rewrite_eq(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(EQUAL_EVAL);
  BZLA_APPLY_RW_RULE(EQUAL_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_ite(const Node& node)
{
  // TODO
  return node;
}

/* BV rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_bv_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_ADD_EVAL);
  BZLA_APPLY_RW_RULE(BV_ADD_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_AND_EVAL);
  BZLA_APPLY_RW_RULE(BV_AND_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ashr(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_ASHR_EVAL);
  BZLA_APPLY_RW_RULE(BV_ASHR_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_concat(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_CONCAT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_extract(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_MUL_EVAL);
  BZLA_APPLY_RW_RULE(BV_MUL_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_not(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_NOT_EVAL);
  BZLA_APPLY_RW_RULE(BV_NOT_BV_NOT);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shl(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_SHL_EVAL);
  BZLA_APPLY_RW_RULE(BV_SHL_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shr(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_SHR_EVAL);
  BZLA_APPLY_RW_RULE(BV_SHR_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_slt(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_SLT_EVAL);
  BZLA_APPLY_RW_RULE(BV_SLT_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_udiv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_UDIV_EVAL);
  BZLA_APPLY_RW_RULE(BV_UDIV_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ult(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_ULT_EVAL);
  BZLA_APPLY_RW_RULE(BV_ULT_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_urem(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_UREM_EVAL);
  BZLA_APPLY_RW_RULE(BV_UREM_SPECIAL_CONST);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_xor(const Node& node)
{
  // TODO
  return node;
}

/* Eliminated operators */

BZLA_ELIM_KIND_IMPL(bv_nand, BV_NAND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_neg, BV_NEG_ELIM)
BZLA_ELIM_KIND_IMPL(bv_nor, BV_NOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_or, BV_OR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redand, BV_REDAND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redor, BV_REDOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redxor, BV_REDXOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_repeat, BV_REPEAT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_rol, BV_ROL_ELIM)
BZLA_ELIM_KIND_IMPL(bv_roli, BV_ROLI_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ror, BV_ROR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_rori, BV_RORI_ELIM)
BZLA_ELIM_KIND_IMPL(bv_saddo, BV_SADDO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sdiv, BV_SDIV_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sdivo, BV_SDIVO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sge, BV_SGE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sgt, BV_SGT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sign_extend, BV_SIGN_EXTEND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sle, BV_SLE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_smod, BV_SMOD_ELIM)
// BZLA_ELIM_KIND_IMPL(bv_smulo, BV_SMULO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_srem, BV_SREM_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ssubo, BV_SSUBO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sub, BV_SUB_ELIM)
BZLA_ELIM_KIND_IMPL(bv_uaddo, BV_UADDO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_uge, BV_UGE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ugt, BV_UGT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ule, BV_ULE_ELIM)
// BZLA_ELIM_KIND_IMPL(bv_umulo, BV_UMULO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_usubo, BV_USUBO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_xnor, BV_XNOR_ELIM)
// BZLA_ELIM_KIND_IMPL(bv_xor, BV_XOR_ELIM) do not eliminate
BZLA_ELIM_KIND_IMPL(bv_zero_extend, BV_ZERO_EXTEND_ELIM)

#undef BZLA_ELIM_KIND_IMPL

/* FP rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_fp_abs(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_ABS_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_ADD_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_div(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_DIV_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_inf(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_INF_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_nan(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_NAN_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_NEG_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_normal(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_NORM_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_pos(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_POS_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_subnormal(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_SUBNORM_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_zero(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_ZERO_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_le(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_LE_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_lt(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_LT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_max(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_fp_min(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_fp_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_MUL_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_NEG_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rem(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_REM_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rti(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_RTI_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_sqrt(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_SQRT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_bv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_BV_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_fp(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_FP_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_sbv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_SBV_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_ubv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_UBV_EVAL);
  // TODO

DONE:
  return res;
}

/* Array rewrites ----------------------------------------------------------- */

Node
Rewriter::rewrite_apply(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_lambda(const Node& node)
{
  // TODO
  return node;
}

/* Quant rewrites ----------------------------------------------------------- */

Node
Rewriter::rewrite_forall(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_exists(const Node& node)
{
  // TODO
  return node;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
