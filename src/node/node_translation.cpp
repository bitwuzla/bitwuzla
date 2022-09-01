#include "node/node_translation.h"

#include <unordered_map>
#include <vector>

extern "C" {
#include "utils/bzlanodeiter.h"
}

#include "bzlabvstruct.h"

namespace bzla::node {

type::Type
translate_bzla_sort(NodeManager &nm,
                    Bzla *bzla,
                    BzlaNode *n,
                    BzlaSortId sort_id)
{
  if (bzla_sort_is_bv(bzla, sort_id))
  {
    return nm.mk_bv_type(bzla_sort_bv_get_width(bzla, sort_id));
  }
  else if (bzla_sort_is_fp(bzla, sort_id))
  {
    return nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort_id),
                         bzla_sort_fp_get_exp_width(bzla, sort_id));
  }
  else if (bzla_sort_is_rm(bzla, sort_id))
  {
    return nm.mk_rm_type();
  }

  if (n)
  {
    if (bzla_node_is_array(n))
    {
      return nm.mk_array_type(
          translate_bzla_sort(
              nm, bzla, nullptr, bzla_sort_array_get_index(bzla, sort_id)),
          translate_bzla_sort(
              nm, bzla, nullptr, bzla_sort_array_get_element(bzla, sort_id)));
    }
  }

  if (bzla_sort_is_fun(bzla, sort_id))
  {
    std::vector<type::Type> types;
    auto codomain =
        bzla_sort_get_by_id(bzla, bzla_sort_fun_get_codomain(bzla, sort_id));
    for (size_t i = 0; i < codomain->tuple.num_elements; ++i)
    {
      types.push_back(translate_bzla_sort(
          nm, bzla, nullptr, codomain->tuple.elements[i]->id));
    }
    types.push_back(translate_bzla_sort(
        nm, bzla, nullptr, bzla_sort_fun_get_domain(bzla, sort_id)));
    return nm.mk_fun_type(types);
  }
  assert(false);
  return type::Type();
}

Node
translate_bzla_node(NodeManager &nm, BzlaNode *node)
{
  Bzla *bzla = bzla_node_real_addr(node)->bzla;

  std::vector<BzlaNode *> visit{node};
  std::unordered_map<BzlaNode *, Node> cache;

  do
  {
    auto cur = visit.back();
    auto it  = cache.find(cur);

    if (it == cache.end())
    {
      cache.emplace(cur, Node());
      if (bzla_node_is_inverted(cur))
      {
        visit.push_back(bzla_node_real_addr(cur));
      }
      else if (bzla_node_is_apply(cur))
      {
        visit.push_back(cur->e[0]);
        BzlaArgsIterator ait;
        bzla_iter_args_init(&ait, cur->e[1]);
        while (bzla_iter_args_has_next(&ait))
        {
          visit.push_back(bzla_iter_args_next(&ait));
        }
      }
      else if (bzla_node_is_update(cur))
      {
        visit.push_back(cur->e[0]);
        assert(cur->e[1]->arity == 1);
        visit.push_back(cur->e[1]->e[0]);
        visit.push_back(cur->e[2]);
      }
      else
      {
        assert(bzla_node_is_regular(cur));
        for (size_t i = 0; i < cur->arity; ++i)
        {
          visit.push_back(cur->e[i]);
        }
      }
      continue;
    }
    else if (it->second.is_null())
    {
      std::vector<Node> children;

      if (bzla_node_is_inverted(cur))
      {
        auto itt = cache.find(bzla_node_real_addr(cur));
        assert(itt != cache.end());
        children.push_back(itt->second);
      }
      else if (bzla_node_is_apply(cur))
      {
        auto itt = cache.find(cur->e[0]);
        assert(itt != cache.end());
        children.push_back(itt->second);
        BzlaArgsIterator ait;
        bzla_iter_args_init(&ait, cur);
        while (bzla_iter_args_has_next(&ait))
        {
          itt = cache.find(bzla_iter_args_next(&ait));
          assert(itt != cache.end());
          children.push_back(itt->second);
        }
      }
      else if (bzla_node_is_update(cur))
      {
        auto itt = cache.find(cur->e[0]);
        assert(itt != cache.end());
        children.push_back(itt->second);
        itt = cache.find(cur->e[1]->e[0]);
        assert(itt != cache.end());
        children.push_back(itt->second);
        itt = cache.find(cur->e[2]);
        assert(itt != cache.end());
        children.push_back(itt->second);
      }
      else
      {
        assert(bzla_node_is_regular(cur));
        for (size_t i = 0; i < cur->arity; ++i)
        {
          auto itt = cache.find(cur->e[i]);
          assert(itt != cache.end());
          children.push_back(itt->second);
        }
      }

      Node res;
      // Handle not as separate kind
      if (bzla_node_is_inverted(cur))
      {
        res = nm.mk_node(Kind::BV_NOT, children);
      }
      else
      {
        switch (bzla_node_get_kind(cur))
        {
          case BZLA_BV_CONST_NODE: {
            BzlaBitVector *bv = bzla_node_bv_const_get_bits(cur);
            res               = nm.mk_value(*bv->d_bv);
          }
          break;
          case BZLA_FP_CONST_NODE: assert(false); break;
          case BZLA_RM_CONST_NODE: assert(false); break;
          case BZLA_UF_NODE:
          case BZLA_PARAM_NODE:
          case BZLA_VAR_NODE: {
            type::Type t =
                translate_bzla_sort(nm, bzla, cur, bzla_node_get_sort_id(cur));
            if (bzla_node_get_kind(cur) == BZLA_PARAM_NODE)
            {
              res = nm.mk_var(t);
            }
            else
            {
              res = nm.mk_const(t);
            }
          }
          break;
          case BZLA_BV_SLICE_NODE:
            res = nm.mk_node(Kind::BV_EXTRACT,
                             children,
                             {bzla_node_bv_slice_get_upper(cur),
                              bzla_node_bv_slice_get_lower(cur)});
            break;
          case BZLA_FP_ABS_NODE:
            res = nm.mk_node(Kind::FP_ABS, children);
            break;
          case BZLA_FP_IS_INF_NODE:
            res = nm.mk_node(Kind::FP_IS_INF, children);
            break;
          case BZLA_FP_IS_NAN_NODE:
            res = nm.mk_node(Kind::FP_IS_NAN, children);
            break;
          case BZLA_FP_IS_NEG_NODE:
            res = nm.mk_node(Kind::FP_IS_NEG, children);
            break;
          case BZLA_FP_IS_NORM_NODE:
            res = nm.mk_node(Kind::FP_IS_NORM, children);
            break;
          case BZLA_FP_IS_POS_NODE:
            res = nm.mk_node(Kind::FP_IS_POS, children);
            break;
          case BZLA_FP_IS_SUBNORM_NODE:
            res = nm.mk_node(Kind::FP_IS_SUBNORM, children);
            break;
          case BZLA_FP_IS_ZERO_NODE:
            res = nm.mk_node(Kind::FP_IS_ZERO, children);
            break;
          case BZLA_FP_NEG_NODE:
            res = nm.mk_node(Kind::FP_IS_NEG, children);
            break;
          case BZLA_FP_TO_FP_BV_NODE: {
            auto sort = bzla_node_get_sort_id(cur);
            res       = nm.mk_node(Kind::FP_TO_FP_FROM_BV,
                             children,
                             {bzla_sort_fp_get_exp_width(bzla, sort),
                                    bzla_sort_fp_get_sig_width(bzla, sort)});
          }
          break;

          case BZLA_BV_AND_NODE:
            res = nm.mk_node(Kind::BV_AND, children);
            break;

          case BZLA_FUN_EQ_NODE:
          case BZLA_RM_EQ_NODE:
          case BZLA_BV_EQ_NODE:
          case BZLA_FP_EQ_NODE: res = nm.mk_node(Kind::EQUAL, children); break;

          case BZLA_BV_ADD_NODE:
            res = nm.mk_node(Kind::BV_ADD, children);
            break;
          case BZLA_BV_MUL_NODE:
            res = nm.mk_node(Kind::BV_MUL, children);
            break;
          case BZLA_BV_ULT_NODE:
            res = nm.mk_node(Kind::BV_ULT, children);
            break;
          case BZLA_BV_SLL_NODE:
            res = nm.mk_node(Kind::BV_SHL, children);
            break;
          case BZLA_BV_SLT_NODE:
            res = nm.mk_node(Kind::BV_SLT, children);
            break;
          case BZLA_BV_SRL_NODE:
            res = nm.mk_node(Kind::BV_SHR, children);
            break;
          case BZLA_BV_UDIV_NODE:
            res = nm.mk_node(Kind::BV_UDIV, children);
            break;
          case BZLA_BV_UREM_NODE:
            res = nm.mk_node(Kind::BV_UREM, children);
            break;
          case BZLA_BV_CONCAT_NODE:
            res = nm.mk_node(Kind::BV_CONCAT, children);
            break;
          case BZLA_FP_LTE_NODE: res = nm.mk_node(Kind::FP_LE, children); break;
          case BZLA_FP_LT_NODE: res = nm.mk_node(Kind::FP_LT, children); break;
          case BZLA_FP_MIN_NODE:
            res = nm.mk_node(Kind::FP_MIN, children);
            break;
          case BZLA_FP_MAX_NODE:
            res = nm.mk_node(Kind::FP_MAX, children);
            break;
          case BZLA_FP_SQRT_NODE:
            res = nm.mk_node(Kind::FP_SQRT, children);
            break;
          case BZLA_FP_REM_NODE:
            res = nm.mk_node(Kind::FP_REM, children);
            break;
          case BZLA_FP_RTI_NODE:
            res = nm.mk_node(Kind::FP_RTI, children);
            break;
          case BZLA_FP_TO_SBV_NODE:
            res = nm.mk_node(
                Kind::FP_TO_SBV, children, {bzla_node_bv_get_width(bzla, cur)});
            break;
          case BZLA_FP_TO_UBV_NODE:
            res = nm.mk_node(
                Kind::FP_TO_UBV, children, {bzla_node_bv_get_width(bzla, cur)});
            break;
          case BZLA_FP_TO_FP_FP_NODE:
            res = nm.mk_node(Kind::FP_TO_FP_FROM_FP,
                             children,
                             {bzla_node_fp_get_exp_width(bzla, cur),
                              bzla_node_fp_get_sig_width(bzla, cur)});
            break;
          case BZLA_FP_TO_FP_SBV_NODE:
            res = nm.mk_node(Kind::FP_TO_FP_FROM_SBV,
                             children,
                             {bzla_node_fp_get_exp_width(bzla, cur),
                              bzla_node_fp_get_sig_width(bzla, cur)});
            break;
          case BZLA_FP_TO_FP_UBV_NODE:
            res = nm.mk_node(Kind::FP_TO_FP_FROM_UBV,
                             children,
                             {bzla_node_fp_get_exp_width(bzla, cur),
                              bzla_node_fp_get_sig_width(bzla, cur)});
            break;
          case BZLA_APPLY_NODE: res = nm.mk_node(Kind::APPLY, children); break;
          case BZLA_FORALL_NODE:
            res = nm.mk_node(Kind::FORALL, children);
            break;
          case BZLA_EXISTS_NODE:
            res = nm.mk_node(Kind::EXISTS, children);
            break;
          case BZLA_LAMBDA_NODE:
            res = nm.mk_node(Kind::LAMBDA, children);
            break;
          case BZLA_COND_NODE: res = nm.mk_node(Kind::ITE, children); break;
          case BZLA_FP_ADD_NODE:
            res = nm.mk_node(Kind::FP_ADD, children);
            break;
          case BZLA_FP_MUL_NODE:
            res = nm.mk_node(Kind::FP_MUL, children);
            break;
          case BZLA_FP_DIV_NODE:
            res = nm.mk_node(Kind::FP_DIV, children);
            break;
          case BZLA_UPDATE_NODE: res = nm.mk_node(Kind::STORE, children); break;
          case BZLA_FP_FMA_NODE:
            res = nm.mk_node(Kind::FP_FMA, children);
            break;

          case BZLA_ARGS_NODE:
          case BZLA_INVALID_NODE:
          case BZLA_PROXY_NODE:
          case BZLA_NUM_OPS_NODE: assert(false); break;
        }
      }
      assert(!res.is_null());
      it->second = res;
    }

    visit.pop_back();
  } while (!visit.empty());

  auto it = cache.find(node);
  assert(it != cache.end());
  return it->second;
}

}  // namespace bzla::node
