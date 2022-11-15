#include "solver/fp/word_blaster.h"

#include <sstream>

#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "solver/fp/symfpu_wrapper.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/unpackedFloat.h"

namespace bzla {
namespace fp {

namespace {
std::string
create_component_symbol(const Node& node, const std::string& s)
{
  assert(!node.is_null());
  assert(!s.empty());
  return "_fp_var_" + std::to_string(node.id()) + s + "_component_";
}
}  // namespace

struct WordBlaster::Internal
{
  SymFpuSymRMMap d_rm_map;
  SymFpuSymPropMap d_prop_map;
  SymUBVMap d_ubv_map;
  SymSBVMap d_sbv_map;
  UnpackedFloatMap d_unpacked_float_map;
  PackedFloatMap d_packed_float_map;
};

/* --- WordBlaster public --------------------------------------------------- */

WordBlaster::WordBlaster(SolvingContext& context) : d_ctx(context)
{
  d_internal.reset(new Internal());
}

WordBlaster::~WordBlaster() {}

Node
WordBlaster::word_blast(const Node& node)
{
  assert((node.type().is_bv() && node.num_children()
          && (node[0].type().is_fp() || node[0].type().is_rm()))
         || node.type().is_fp() || node.type().is_rm());

  Node res;
  node::node_ref_vector visit{node};
  node::unordered_node_ref_map<bool> visited;
  NodeManager& nm = NodeManager::get();

  do
  {
    const Node& cur = visit.back();
    // TODO: assert that cur is not parameterized
    visit.pop_back();

    if (d_internal->d_prop_map.find(cur) != d_internal->d_prop_map.end()
        || d_internal->d_rm_map.find(cur) != d_internal->d_rm_map.end()
        || d_internal->d_sbv_map.find(cur) != d_internal->d_sbv_map.end()
        || d_internal->d_ubv_map.find(cur) != d_internal->d_ubv_map.end()
        || d_internal->d_unpacked_float_map.find(cur)
               != d_internal->d_unpacked_float_map.end())
    {
      continue;
    }

    node::Kind kind = cur.kind();
    if (visited.find(cur) == visited.end())
    {
      visited.emplace(cur, false);
      visit.push_back(cur);

      /* We treat applies and quantifiers as variables. */
      // TODO: Should this be a leaf node check? Why is exists not included?
      //       what about select?
      if (kind != node::Kind::APPLY)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (!visited.at(cur))
    {
      const Type& type = cur.type();
      if (kind == node::Kind::ITE && cur[1].type().is_rm())
      {
        assert(d_internal->d_rm_map.find(cur[1]) != d_internal->d_rm_map.end());
        assert(d_internal->d_rm_map.find(cur[2]) != d_internal->d_rm_map.end());
        d_internal->d_rm_map.emplace(
            cur,
            symfpu::ite<SymFpuSymProp, SymFpuSymRM>::iteOp(
                SymFpuSymProp(cur[0]),
                d_internal->d_rm_map.at(cur[1]),
                d_internal->d_rm_map.at(cur[2])));
      }
      else if (kind == node::Kind::ITE && cur[1].type().is_fp())
      {
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[2])
               != d_internal->d_unpacked_float_map.end());

        // Consruct ITEs over unpacked float components
        auto uf1 = d_internal->d_unpacked_float_map.at(cur[1]);
        auto uf2 = d_internal->d_unpacked_float_map.at(cur[2]);

        Node nan = nm.mk_node(
            node::Kind::ITE,
            {cur[0], uf1.getNaN().getNode(), uf2.getNaN().getNode()});
        Node inf = nm.mk_node(
            node::Kind::ITE,
            {cur[0], uf1.getInf().getNode(), uf2.getInf().getNode()});
        Node zero = nm.mk_node(
            node::Kind::ITE,
            {cur[0], uf1.getZero().getNode(), uf2.getZero().getNode()});
        Node sign = nm.mk_node(
            node::Kind::ITE,
            {cur[0], uf1.getSign().getNode(), uf2.getSign().getNode()});
        Node exp = nm.mk_node(
            node::Kind::ITE,
            {cur[0], uf1.getExponent().getNode(), uf2.getExponent().getNode()});
        Node sig = nm.mk_node(node::Kind::ITE,
                              {cur[0],
                               uf1.getSignificand().getNode(),
                               uf2.getSignificand().getNode()});

        d_internal->d_unpacked_float_map.emplace(
            cur, SymUnpackedFloat(nan, inf, zero, sign, exp, sig));
      }
      else if (type.is_rm() && cur.is_value())
      {
        d_internal->d_rm_map.emplace(cur, SymFpuSymRM(cur));
      }
      else if (type.is_rm() && (cur.is_const() || kind == node::Kind::APPLY))
      {
        SymFpuSymRM rmvar(cur);
        d_internal->d_rm_map.emplace(cur, rmvar);
        d_additional_assertions.push_back(rmvar.valid().getNode());
      }
      else if (type.is_fp() && cur.is_value())
      {
        d_internal->d_unpacked_float_map.emplace(
            cur, *cur.value<FloatingPoint>().unpacked());
      }
      else if (type.is_fp() && (cur.is_const() || kind == node::Kind::APPLY))
      {
        Node inf =
            nm.mk_const(nm.mk_bool_type(), create_component_symbol(cur, "inf"));
        Node nan =
            nm.mk_const(nm.mk_bool_type(), create_component_symbol(cur, "nan"));
        Node sign = nm.mk_const(nm.mk_bool_type(),
                                create_component_symbol(cur, "sign"));
        Node zero = nm.mk_const(nm.mk_bool_type(),
                                create_component_symbol(cur, "zero"));
        Node exp =
            nm.mk_const(nm.mk_bv_type(SymUnpackedFloat::exponentWidth(type)),
                        create_component_symbol(cur, "exp"));
        Node sig =
            nm.mk_const(nm.mk_bv_type(SymUnpackedFloat::significandWidth(type)),
                        create_component_symbol(cur, "sig"));

        SymUnpackedFloat uf(nan, inf, zero, sign, exp, sig);
        d_internal->d_unpacked_float_map.emplace(cur, uf);
        d_additional_assertions.push_back(uf.valid(type).getNode());
      }
      else if (kind == node::Kind::EQUAL && node[0].type().is_fp())
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::smtlibEqual<SymFpuSymTraits>(
                FloatingPointTypeInfo(cur[0].type()),
                d_internal->d_unpacked_float_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1])));
      }
      else if (kind == node::Kind::EQUAL && node[0].type().is_rm())
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_rm_map.find(cur[1]) != d_internal->d_rm_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            d_internal->d_rm_map.at(cur[0]) == d_internal->d_rm_map.at(cur[1]));
      }
      else if (kind == node::Kind::FP_ABS)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::absolute<SymFpuSymTraits>(
                type, d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_NEG)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::negate<SymFpuSymTraits>(
                type, d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_IS_NORM)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::isNormal<SymFpuSymTraits>(
                cur[0].type(), d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_IS_SUBNORM)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::isSubnormal<SymFpuSymTraits>(
                cur[0].type(), d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_IS_ZERO)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::isZero<SymFpuSymTraits>(
                cur[0].type(), d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_IS_INF)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::isInfinite<SymFpuSymTraits>(
                cur[0].type(), d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_IS_NAN)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::isNaN<SymFpuSymTraits>(
                cur[0].type(), d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_IS_NEG)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::isNegative<SymFpuSymTraits>(
                cur[0].type(), d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_IS_POS)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::isPositive<SymFpuSymTraits>(
                cur[0].type(), d_internal->d_unpacked_float_map.at(cur[0])));
      }
      else if (kind == node::Kind::FP_LE)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::lessThanOrEqual<SymFpuSymTraits>(
                cur[0].type(),
                d_internal->d_unpacked_float_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1])));
      }
      else if (kind == node::Kind::FP_LT)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_prop_map.emplace(
            cur,
            symfpu::lessThan<SymFpuSymTraits>(
                cur[0].type(),
                d_internal->d_unpacked_float_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1])));
      }
      else if (kind == node::Kind::FP_MIN || kind == node::Kind::FP_MAX)
      {
        assert(cur.num_children() == 2);
        std::vector<Node> args{min_max_uf(cur)};
        for (size_t i = 0, n = cur.num_children(); i < n; ++i)
        {
          assert(d_internal->d_unpacked_float_map.find(cur[i])
                 != d_internal->d_unpacked_float_map.end());
          if (d_internal->d_packed_float_map.find(cur[i])
              == d_internal->d_packed_float_map.end())
          {
            d_internal->d_packed_float_map.emplace(
                cur[i],
                symfpu::pack(cur[i].type(),
                             d_internal->d_unpacked_float_map.at(cur[i])));
          }
          args.push_back(d_internal->d_packed_float_map.at(cur[i]).getNode());
        }
        Node apply = nm.mk_node(node::Kind::APPLY, args);
        if (kind == node::Kind::FP_MIN)
        {
          d_internal->d_unpacked_float_map.emplace(
              cur,
              symfpu::min<SymFpuSymTraits>(
                  type,
                  d_internal->d_unpacked_float_map.at(cur[0]),
                  d_internal->d_unpacked_float_map.at(cur[1]),
                  apply));
        }
        else
        {
          d_internal->d_unpacked_float_map.emplace(
              cur,
              symfpu::max<SymFpuSymTraits>(
                  type,
                  d_internal->d_unpacked_float_map.at(cur[0]),
                  d_internal->d_unpacked_float_map.at(cur[1]),
                  apply));
        }
      }
      else if (kind == node::Kind::FP_REM)
      {
        assert(d_internal->d_unpacked_float_map.find(cur[0])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::remainder<SymFpuSymTraits>(
                type,
                d_internal->d_unpacked_float_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1])));
      }
      else if (kind == node::Kind::FP_SQRT)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::sqrt<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1])));
      }
      else if (kind == node::Kind::FP_RTI)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::roundToIntegral<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1])));
      }
      else if (kind == node::Kind::FP_ADD)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[2])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::add<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1]),
                d_internal->d_unpacked_float_map.at(cur[2]),
                SymFpuSymProp(true)));
      }
      else if (kind == node::Kind::FP_MUL)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[2])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::multiply<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1]),
                d_internal->d_unpacked_float_map.at(cur[2])));
      }
      else if (kind == node::Kind::FP_DIV)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[2])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::divide<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1]),
                d_internal->d_unpacked_float_map.at(cur[2])));
      }
      else if (kind == node::Kind::FP_FMA)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[2])
               != d_internal->d_unpacked_float_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[3])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::fma<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1]),
                d_internal->d_unpacked_float_map.at(cur[2]),
                d_internal->d_unpacked_float_map.at(cur[3])));
      }
      else if (kind == node::Kind::FP_TO_SBV || kind == node::Kind::FP_TO_UBV)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        uint64_t size = type.bv_size();
        Node apply =
            nm.mk_node(node::Kind::APPLY, {sbv_ubv_uf(cur), cur[0], cur[1]});
        if (kind == node::Kind::FP_TO_SBV)
        {
          d_internal->d_sbv_map.emplace(
              cur,
              symfpu::convertFloatToSBV<SymFpuSymTraits>(
                  cur[1].type(),
                  d_internal->d_rm_map.at(cur[0]),
                  d_internal->d_unpacked_float_map.at(cur[1]),
                  size,
                  SymFpuSymBV<true>(apply)));
        }
        else
        {
          d_internal->d_ubv_map.emplace(
              cur,
              symfpu::convertFloatToUBV<SymFpuSymTraits>(
                  cur[1].type(),
                  d_internal->d_rm_map.at(cur[0]),
                  d_internal->d_unpacked_float_map.at(cur[1]),
                  size,
                  SymFpuSymBV<false>(apply)));
        }
      }
      else if (kind == node::Kind::FP_TO_FP_FROM_BV)
      {
        assert(cur[0].type().is_bv());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::unpack<SymFpuSymTraits>(type, SymFpuSymBV<false>(cur[0])));
      }
      else if (kind == node::Kind::FP_TO_FP_FROM_FP)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(d_internal->d_unpacked_float_map.find(cur[1])
               != d_internal->d_unpacked_float_map.end());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::convertFloatToFloat<SymFpuSymTraits>(
                cur[1].type(),
                type,
                d_internal->d_rm_map.at(cur[0]),
                d_internal->d_unpacked_float_map.at(cur[1])));
      }
      else if (kind == node::Kind::FP_TO_FP_FROM_SBV)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(cur[1].type().is_bv());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::convertSBVToFloat<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                SymFpuSymBV<true>(cur[1])));
      }
      else if (kind == node::Kind::FP_TO_FP_FROM_UBV)
      {
        assert(d_internal->d_rm_map.find(cur[0]) != d_internal->d_rm_map.end());
        assert(cur[1].type().is_bv());
        d_internal->d_unpacked_float_map.emplace(
            cur,
            symfpu::convertUBVToFloat<SymFpuSymTraits>(
                type,
                d_internal->d_rm_map.at(cur[0]),
                SymFpuSymBV<false>(cur[1])));
      }
      visited.at(cur) = 1;
    }
    else
    {
      assert(visited.at(cur) == 1);
      continue;
    }
  } while (!visit.empty());

  if (d_internal->d_prop_map.find(node) != d_internal->d_prop_map.end())
  {
    assert(node.type().is_bool());
    res = d_internal->d_prop_map.at(node).getNode();
  }
  else if (d_internal->d_rm_map.find(node) != d_internal->d_rm_map.end())
  {
    assert(node.type().is_rm());
    res = d_internal->d_rm_map.at(node).getNode();
  }
  else if (d_internal->d_sbv_map.find(node) != d_internal->d_sbv_map.end())
  {
    assert(node.kind() == node::Kind::FP_TO_SBV);
    res = d_internal->d_sbv_map.at(node).getNode();
  }
  else if (d_internal->d_ubv_map.find(node) != d_internal->d_ubv_map.end())
  {
    assert(node.kind() == node::Kind::FP_TO_UBV);
    res = d_internal->d_ubv_map.at(node).getNode();
  }
  else
  {
    assert(d_internal->d_unpacked_float_map.find(node)
           != d_internal->d_unpacked_float_map.end());
    d_internal->d_packed_float_map.emplace(
        node,
        symfpu::pack(node.type(), d_internal->d_unpacked_float_map.at(node)));
    res = d_internal->d_packed_float_map.at(node).getNode();
  }
  assert(!res.is_null());
  return res;
}

Node
WordBlaster::get_word_blasted_node(const Node& node)
{
  assert(!node.is_null());

  if (d_internal->d_packed_float_map.find(node)
      != d_internal->d_packed_float_map.end())
  {
    return d_internal->d_packed_float_map.at(node).getNode();
  }

  if (node.type().is_bool()
      && d_internal->d_prop_map.find(node) != d_internal->d_prop_map.end())
  {
    return d_internal->d_prop_map.at(node).getNode();
  }

  if (node.type().is_rm()
      && d_internal->d_rm_map.find(node) != d_internal->d_rm_map.end())
  {
    return d_internal->d_rm_map.at(node).getNode();
  }

  if (d_internal->d_unpacked_float_map.find(node)
      != d_internal->d_unpacked_float_map.end())
  {
    d_internal->d_packed_float_map.emplace(
        node,
        symfpu::pack(node.type(), d_internal->d_unpacked_float_map.at(node)));
    return d_internal->d_packed_float_map.at(node).getNode();
  }

  return word_blast(node);
}

void
WordBlaster::get_introduced_ufs(node::node_ref_vector& ufs)
{
  for (const auto& p : d_min_max_uf_map)
  {
    ufs.push_back(p.second);
  }
  for (const auto& p : d_sbv_ubv_uf_map)
  {
    ufs.push_back(p.second);
  }
}

void
WordBlaster::add_additional_assertions()
{
  for (const Node& node : d_additional_assertions)
  {
    d_ctx.assert_formula(node);
  }
  d_additional_assertions.clear();
}

/* --- WordBlaster private -------------------------------------------------- */

const Node&
WordBlaster::min_max_uf(const Node& node)
{
  const Type& type = node.type();

  if (d_min_max_uf_map.find(type) != d_min_max_uf_map.end())
  {
    return d_min_max_uf_map.at(type);
  }

  NodeManager& nm  = NodeManager::get();
  size_t nchildren = node.num_children();
  uint64_t size    = type.fp_ieee_bv_size();
  Type type_bv1    = nm.mk_bv_type(1);
  Type type_bv     = nm.mk_bv_type(size);
  std::vector<Type> type_fun_args;
  for (size_t i = 0; i < nchildren; ++i) type_fun_args.push_back(type_bv);
  type_fun_args.push_back(type_bv1);
  Type type_fun = nm.mk_fun_type(type_fun_args);
  d_min_max_uf_map.emplace(
      type_fun,
      nm.mk_const(
          type_fun,
          (node.kind() == node::Kind::FP_MIN ? "_fp_min_uf_" : "_fp_max_uf_")
              + std::to_string(node.id()) + "_"));
  return d_min_max_uf_map.at(type_fun);
}

const Node&
WordBlaster::sbv_ubv_uf(const Node& node)
{
  assert(node[0].type().is_rm());
  assert(node[1].type().is_fp());

  Type type_bv = node.type();
  Type type_fp = node[1].type();
  std::pair<Type, Type> p(type_fp, type_bv);

  if (d_sbv_ubv_uf_map.find(p) != d_sbv_ubv_uf_map.end())
  {
    return d_sbv_ubv_uf_map.at(p);
  }

  NodeManager& nm = NodeManager::get();
  Type type_fun   = nm.mk_fun_type({node[0].type(), type_fp, type_bv});
  d_sbv_ubv_uf_map.emplace(
      type_fun,
      nm.mk_const(
          type_fun,
          (node.kind() == node::Kind::FP_TO_SBV ? "_fp_sbv_uf_" : "_fp_ubv_uf_")
              + std::to_string(node.id()) + "_"));
  return d_sbv_ubv_uf_map.at(p);
}

/* -------------------------------------------------------------------------- */
}  // namespace fp
}  // namespace bzla
