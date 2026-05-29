/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/bv_inverter.h"

#include <cassert>

#include "node/node_kind.h"
#include "node/node_utils.h"

namespace bzla::bv {

/* --- BvInverter public ---------------------------------------------------- */

BvInverter::BvInverter(Env& env) : d_env(env), d_nm(env.nm()) {}

BvInverter::~BvInverter() {}

/* -------------------------------------------------------------------------- */

namespace {
/** @return True if x occurs in given node. */
bool check_for_x(const Node& node, const Node& x)
{
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    auto cur    = visit.back();
    auto [it, inserted] = cache.emplace(cur);
    visit.pop_back();
    if (cur == x)
    {
      return true;
    }
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

}
std::pair<Node, std::vector<Node>>
BvInverter::invert(const Node& node, const Node& x)
{
  Node res;
  std::vector<Node> conds;
  std::unordered_map<Node, Node> subst_cache;

  // compute path to x
  auto path = compute_path(node, x);
  if (path.empty())
  {
    return {Node(), {}};
  }

  // ///
  //  {
  //   std::cout << "## path:" << std::endl;
  //   Node cur = node;
  //   while (cur != x)
  //   {
  //     std::cout << cur << ": " << path[cur] << std::endl;
  //     cur = cur[path[cur]];
  //   }
  // }
  ///

  // compute inverse for top-level predicate
  Node cur       = node;
  size_t idx     = path.at(cur);
  Kind predicate = cur.kind();
  bool negate    = predicate == Kind::NOT;
  if (negate)
  {
    cur       = cur[idx];
    idx       = path.at(cur);
    predicate = cur.kind();
  }

  Node t, next;
  if (predicate == Kind::AND)
  {
    t = d_nm.mk_value(!negate);
  }
  else
  {
    if (predicate == Kind::EQUAL && !negate)
    {
      size_t idx_x = idx;
      auto it      = path.find(cur[idx]);
      next         = cur[idx];
      if (next != x && it != path.end())
      {
        idx_x = it->second;
        next  = cur[idx][idx_x];
      }
      t = inverse(cur[idx], idx_x, cur[1 - idx]);
    }
    if (t.is_null())
    {
      Node icond;
      std::tie(icond, next) = ic(cur, idx, path, negate);
      Node _xx              = d_nm.mk_const(next.type());
      Node pred = utils::substitute(d_nm, cur, {{next, _xx}}, subst_cache);
      conds.push_back(d_nm.mk_node(Kind::IMPLIES, {icond, pred}));
      t = _xx;
    }
    cur = next;
  }
  while (cur != x)
  {
    idx      = path.at(cur);
    next     = cur[idx];
    Node inv = inverse(cur, idx, t);
    if (inv.is_null())
    {
      Node icond = ic(Kind::EQUAL, cur, t, 0, idx);
      Node _xx   = d_nm.mk_const(next.type());
      Node pred  = d_nm.mk_node(Kind::EQUAL,
                                {d_nm.mk_node(cur.kind(),
                                              {idx == 0 ? _xx : cur[1 - idx],
                                              idx == 0 ? cur[1 - idx] : _xx}),
                                 t});
      conds.push_back(d_nm.mk_node(Kind::IMPLIES, {icond, pred}));
      t = _xx;
    }
    else
    {
      t = inv;
    }
    cur = next;
  }

  if (check_for_x(t, x))
  {
    return {Node(), {}};
  }

  subst_cache.clear();
  for (auto& c : conds)
  {
    c = utils::substitute(d_nm, c, {{x, t}}, subst_cache);
    assert(!check_for_x(c, x));
  }
  return {t, conds};
}

/* -------------------------------------------------------------------------- */

Node
BvInverter::ic(const Node& node, const Node& t, size_t idx)
{
  Kind kind = node.kind();
  switch (kind)
  {
    case Kind::AND:
    case Kind::OR:
    case Kind::BV_AND:
    case Kind::BV_OR:
    case Kind::BV_ASHR:
    case Kind::BV_CONCAT:
    case Kind::BV_MUL:
    case Kind::BV_SHR:
    case Kind::BV_SHL:
    case Kind::BV_SIGN_EXTEND:
    case Kind::BV_UREM:
    case Kind::BV_UDIV: return ic(Kind::EQUAL, node, t, 0, idx);

    case Kind::BV_SLT:
    case Kind::BV_SGT:
      if ((kind == Kind::BV_SLT && idx == 0)
          || (kind == Kind::BV_SGT && idx == 1))
      {
        // x <_s t
        // t >_s x
        // IC: (distinct t min_signed_[w])
        return d_nm.mk_node(
            Kind::DISTINCT,
            {t, d_nm.mk_value(BitVector::mk_min_signed(t.type().bv_size()))});
      }
      // x >_s t
      // t <_s x
      // IC: (distinct t max_signed_[w])
      return d_nm.mk_node(
          Kind::DISTINCT,
          {t, d_nm.mk_value(BitVector::mk_max_signed(t.type().bv_size()))});
    case Kind::BV_ULT:
    case Kind::BV_UGT:
      if ((kind == Kind::BV_ULT && idx == 0)
          || (kind == Kind::BV_UGT && idx == 1))
      {
        // x <_u t
        // t >_u x
        // IC: (distinct t (_ bv0 w))
        return d_nm.mk_node(
            Kind::DISTINCT,
            {t, d_nm.mk_value(BitVector::mk_zero(t.type().bv_size()))});
      }
      // x >_u s
      // t <_u x
      // IC: (distinct t (bvnot (_ bv0 w)))
      return d_nm.mk_node(
          Kind::DISTINCT,
          {t, d_nm.mk_value(BitVector::mk_ones(t.type().bv_size()))});

    default:
      assert(kind == Kind::BV_UGE || kind == Kind::BV_ULE
             || kind == Kind::BV_SGE || kind == Kind::BV_SLE
             || kind == Kind::DISTINCT || kind == Kind::EQUAL);
      // x >=_u s = t
      // x <=_u s = t
      // x >=_s s = t
      // x <=_s s = t
      // x != t
      // x = t
      // IC: true
      return d_nm.mk_value(true);
  }
}
/* --- BvInverter private --------------------------------------------------- */

bool
BvInverter::is_invertible(const Node& node) const
{
  Kind kind = node.kind();
  switch (kind)
  {
    case Kind::AND:
    case Kind::OR:
    case Kind::EQUAL:
    case Kind::DISTINCT:
    case Kind::NOT:

    case Kind::BV_ADD:
    case Kind::BV_AND:
    case Kind::BV_OR:
    case Kind::BV_ASHR:
    case Kind::BV_ULT:
    case Kind::BV_UGT:
    case Kind::BV_ULE:
    case Kind::BV_UGE:
    case Kind::BV_SLT:
    case Kind::BV_SGT:
    case Kind::BV_SLE:
    case Kind::BV_SGE:
    case Kind::BV_NOT:
    case Kind::BV_CONCAT:
    case Kind::BV_MUL:
    case Kind::BV_UDIV:
    case Kind::BV_UREM:
    case Kind::BV_SHL:
    case Kind::BV_SHR: return true;

    default:
      assert(kind != Kind::BV_COMP);
      assert(kind != Kind::BV_DEC);
      assert(kind != Kind::BV_INC);
      assert(kind != Kind::BV_NAND);
      assert(kind != Kind::BV_NEG);
      assert(kind != Kind::BV_NEG);
      assert(kind != Kind::BV_NEGO);
      assert(kind != Kind::BV_NOR);
      assert(kind != Kind::BV_REDAND);
      assert(kind != Kind::BV_REDOR);
      assert(kind != Kind::BV_REDXOR);
      assert(kind != Kind::BV_REPEAT);
      assert(kind != Kind::BV_ROL);
      assert(kind != Kind::BV_ROLI);
      assert(kind != Kind::BV_ROR);
      assert(kind != Kind::BV_RORI);
      assert(kind != Kind::BV_SADDO);
      assert(kind != Kind::BV_SDIV);
      assert(kind != Kind::BV_SDIVO);
      assert(kind != Kind::BV_SIGN_EXTEND);
      assert(kind != Kind::BV_SIGN_EXTEND);
      assert(kind != Kind::BV_SMOD);
      assert(kind != Kind::BV_SMULO);
      assert(kind != Kind::BV_SREM);
      assert(kind != Kind::BV_SSUBO);
      assert(kind != Kind::BV_SUB);
      assert(kind != Kind::BV_UADDO);
      assert(kind != Kind::BV_UMULO);
      assert(kind != Kind::BV_USUBO);
      assert(kind != Kind::BV_XNOR);
      assert(kind != Kind::BV_ZERO_EXTEND);
      assert(kind != Kind::IMPLIES);
      assert(kind != Kind::XOR);
      return false;
  }
}

std::unordered_map<Node, size_t>
BvInverter::compute_path(const Node& node, const Node& x) const
{
  std::vector<std::pair<Node, size_t>> visit{{node, 0}};
  std::unordered_map<Node, bool> cache;
  do
  {
    auto [cur, idx]     = visit.back();
    auto [it, inserted] = cache.emplace(cur, true);

    if (cur == x)
    {
      assert(inserted);
      break;
    }
    if (!is_invertible(cur))
    {
      it->second = false;
      visit.pop_back();
      continue;
    }
    if (inserted)
    {
      for (size_t i = 0, n = cur.num_children(); i < n; ++i)
      {
        visit.push_back({cur[i], i});
      }
    }
    else
    {
      it->second = false;
      visit.pop_back();
    }
  } while (!visit.empty());

  std::vector<std::pair<Node, size_t>> path;
  for (const auto& v : visit)
  {
    auto it = cache.find(v.first);
    if (it != cache.end() && it->second)
    {
      path.push_back(std::move(v));
    }
  }

  std::unordered_map<Node, size_t> res;
  for (size_t i = 1, n = path.size(); i < n; ++i)
  {
    res[path[i - 1].first] = path[i].second;
  }
  return res;
}

/* -------------------------------------------------------------------------- */

Node
BvInverter::inverse(const Node& node, size_t idx, const Node& t)
{
  Kind kind = node.kind();

  if (kind == Kind::VARIABLE || kind == Kind::CONSTANT)
  {
    return t;
  }
  if (kind == Kind::NOT || kind == Kind::BV_NOT)
  {
    return d_nm.mk_node(kind, {t});
  }
  const Node& s = node[1 - idx];
  if (kind == Kind::BV_ADD)
  {
    return d_nm.mk_node(Kind::BV_SUB, {t, s});
  }
  if (kind == Kind::BV_XOR)
  {
    return d_nm.mk_node(kind, {t, s});
  }
  if (kind == Kind::BV_MUL && s.is_value())
  {
    const BitVector& s_val = s.value<BitVector>();
    if (s_val.lsb())
    {
      return d_nm.mk_node(kind, {d_nm.mk_value(s_val.bvmodinv()), t});
    }
  }
  // if (kind == Kind::BV_CONCAT)
  // {
  //   // Compute inverse while disregarding that invertibility depend on s,
  //   // i.e., instead of computing the invertibility condition for this case.
  //   // TODO evaluate if this improves performance
  //   uint64_t bw_x = node[idx].type().bv_size();
  //   uint64_t bw_t = t.type().bv_size();
  //   if (idx == 0)
  //   {
  //     // t_x = t[bw(t) - 1: bw(t) - bw(x)]
  //     return d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_t - 1, bw_t - bw_x});
  //   }
  //   // t_x = t[bw(x) - 1: 0]
  //   return d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_x - 1, 0});
  // }
  return Node();
}

/* -------------------------------------------------------------------------- */

std::pair<Node, Node>
BvInverter::ic(const Node& node,
               size_t idx,
               const std::unordered_map<Node, size_t>& path,
               bool negate)
{
  Kind kind = node.kind();
  if (negate)
  {
    switch (kind)
    {
      case Kind::BV_ULT: kind = Kind::BV_UGE; break;
      case Kind::BV_UGT: kind = Kind::BV_ULE; break;
      case Kind::BV_UGE: kind = Kind::BV_ULT; break;
      case Kind::BV_ULE: kind = Kind::BV_UGE; break;
      case Kind::BV_SLT: kind = Kind::BV_SGE; break;
      case Kind::BV_SGT: kind = Kind::BV_SLE; break;
      case Kind::BV_SGE: kind = Kind::BV_SLT; break;
      case Kind::BV_SLE: kind = Kind::BV_SGT; break;
      case Kind::DISTINCT: kind = Kind::EQUAL; break;
      default:
        assert(kind == Kind::EQUAL);
        kind = Kind::DISTINCT;
        break;
    }
  }

  const Node& x = node[idx];
  const Node& s = node[1 - idx];

  std::pair<Node, Node> res;
  switch (x.kind())
  {
    case Kind::BV_AND:
    case Kind::BV_OR:
    case Kind::BV_ASHR:
    case Kind::BV_CONCAT:
    case Kind::BV_MUL:
    case Kind::BV_SHR:
    case Kind::BV_SHL:
    case Kind::BV_SIGN_EXTEND:
    case Kind::BV_UREM:
    case Kind::BV_UDIV: res = ic(kind, x, idx, s, path); break;

    default:
      if ((kind == Kind::BV_ULT && idx == 0)
          || (kind == Kind::BV_UGT && idx == 1))
      {
        // x <_u s
        // s >_u x
        // IC: (distinct s (_ bv0 w))
        res.first = d_nm.mk_node(
            Kind::DISTINCT,
            {s, d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()))});
      }
      else if ((kind == Kind::BV_ULT && idx == 1)
               || (kind == Kind::BV_UGT && idx == 0))
      {
        // x >_u s
        // s <_u x
        // IC: (distinct s (bvnot (_ bv0 w)))
        res.first = d_nm.mk_node(
            Kind::DISTINCT,
            {s, d_nm.mk_value(BitVector::mk_ones(s.type().bv_size()))});
      }
      else if ((kind == Kind::BV_SLT && idx == 0)
               || (kind == Kind::BV_SGT && idx == 1))
      {
        // x <_s s
        // s >_s x
        // IC: (distinct s min_signed_[w])
        res.first = d_nm.mk_node(
            Kind::DISTINCT,
            {s, d_nm.mk_value(BitVector::mk_min_signed(s.type().bv_size()))});
      }
      else if ((kind == Kind::BV_SLT && idx == 1)
               || (kind == Kind::BV_SGT && idx == 0))
      {
        // x >_s s
        // s <_s x
        // IC: (distinct s max_signed_[w])
        res.first = d_nm.mk_node(
            Kind::DISTINCT,
            {s, d_nm.mk_value(BitVector::mk_max_signed(s.type().bv_size()))});
      }
      else
      {
        assert(kind == Kind::BV_UGE || kind == Kind::BV_ULE
               || kind == Kind::BV_SGE || kind == Kind::BV_SLE
               || kind == Kind::DISTINCT || kind == Kind::EQUAL);
        // x >=_u s
        // x <=_u s
        // x >=_s s
        // x <=_s s
        // x != s
        // x = s
        // IC: true
        res.first = d_nm.mk_value(true);
      }
      res.second = x;
  }
  return res;
}

Node
BvInverter::ic(
    Kind predicate, const Node& node, const Node& t, size_t idx, size_t idx_x)
{
  if (idx)
  {
    switch (predicate)
    {
      case Kind::BV_ULT:  // t <u node -> node >u t
        predicate = Kind::BV_UGT;
        break;
      case Kind::BV_ULE:  // t <=u node -> node >=u t
        predicate = Kind::BV_UGE;
        break;
      case Kind::BV_UGT:  // t >u node -> node <u t
        predicate = Kind::BV_ULT;
        break;
      case Kind::BV_UGE:  // t >=u node -> node <=u t
        predicate = Kind::BV_ULE;
        break;
      case Kind::BV_SLT:  // t <s node -> node >s t
        predicate = Kind::BV_SGT;
        break;
      case Kind::BV_SLE:  // t <=s node -> node >=s t
        predicate = Kind::BV_SGE;
        break;
      case Kind::BV_SGT:  // t >s node -> node <s t
        predicate = Kind::BV_SLT;
        break;
      case Kind::BV_SGE:  // t >=s node -> node <=s t
        predicate = Kind::BV_SLE;
        break;
      default:
        assert(predicate == Kind::AND || predicate == Kind::EQUAL
               || predicate == Kind::DISTINCT);
    }
  }
  Kind kind = node.kind();
  switch (kind)
  {
    case Kind::AND: return ic_and(predicate, node, t, idx_x);
    case Kind::OR: return ic_or(predicate, node, t, idx_x);
    case Kind::BV_AND: return ic_bv_and(predicate, node, t, idx_x);
    case Kind::BV_OR: return ic_bv_or(predicate, node, t, idx_x);
    case Kind::BV_ASHR: return ic_bv_ashr(predicate, node, t, idx_x);
    case Kind::BV_CONCAT: return ic_bv_concat(predicate, node, t, idx_x);
    case Kind::BV_MUL: return ic_bv_mul(predicate, node, t, idx_x);
    case Kind::BV_SHR: return ic_bv_shr(predicate, node, t, idx_x);
    case Kind::BV_SHL: return ic_bv_shl(predicate, node, t, idx_x);
    case Kind::BV_SIGN_EXTEND: return ic_bv_sext(predicate, node, t, idx_x);
    case Kind::BV_UREM: return ic_bv_urem(predicate, node, t, idx_x);
    case Kind::BV_UDIV: return ic_bv_udiv(predicate, node, t, idx_x);

    case Kind::BV_SLT:
    case Kind::BV_SGT: {
      Node s = node[1 - idx_x];
      if ((kind == Kind::BV_SLT && idx == 0)
          || (kind == Kind::BV_SGT && idx == 1))
      {
        // x <_s t = t
        // s >_s x = t
        // IC: (distinct t min_signed_[w])
        Node s = node[1 - idx_x];
        return d_nm.mk_node(
            Kind::IMPLIES,
            {t,
             d_nm.mk_node(Kind::DISTINCT,
                          {s,
                           d_nm.mk_value(BitVector::mk_min_signed(
                               s.type().bv_size()))})});
      }
      // x >_s s = t
      // s <_s x = t
      // IC: (distinct t max_signed_[w])
      return d_nm.mk_node(
          Kind::IMPLIES,
          {t,
           d_nm.mk_node(
               Kind::DISTINCT,
               {s,
                d_nm.mk_value(BitVector::mk_max_signed(s.type().bv_size()))})});
    }
    case Kind::BV_ULT:
    case Kind::BV_UGT: {
      Node s = node[1 - idx_x];
      if ((kind == Kind::BV_ULT && idx == 0)
          || (kind == Kind::BV_UGT && idx == 1))
      {
        // x <_u s = t
        // s >_u x = t
        // IC: (distinct t (_ bv0 w))
        return d_nm.mk_node(
            Kind::IMPLIES,
            {t,
             d_nm.mk_node(
                 Kind::DISTINCT,
                 {s, d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()))})});
      }
      // x >_u s = t
      // s <_u x = t
      // IC: (distinct t (bvnot (_ bv0 w)))
      return d_nm.mk_node(
          Kind::IMPLIES,
          {t,
           d_nm.mk_node(
               Kind::DISTINCT,
               {s, d_nm.mk_value(BitVector::mk_ones(s.type().bv_size()))})});
    }

    default:
      assert(kind == Kind::BV_UGE || kind == Kind::BV_ULE
             || kind == Kind::BV_SGE || kind == Kind::BV_SLE
             || kind == Kind::DISTINCT || kind == Kind::EQUAL);
      // x >=_u s = t
      // x <=_u s = t
      // x >=_s s = t
      // x <=_s s = t
      // x != t
      // x = t
      // IC: true
      return d_nm.mk_value(true);
  }
}

std::pair<Node, Node>
BvInverter::ic(Kind predicate,
               const Node& node,
               size_t idx,
               const Node& t,
               const std::unordered_map<Node, size_t>& path)
{
  size_t idx_x = path.at(node);
  return {ic(predicate, node, t, idx, idx_x), node[idx_x]};
}

/* -------------------------------------------------------------------------- */

Node
BvInverter::ic_and(Kind predicate,
                   const Node& node,
                   const Node& t,
                   size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  switch (predicate)
  {
    case Kind::DISTINCT:
      // x & s != t
      // IC: (or s t)
      {
        return d_nm.mk_node(Kind::OR, {s, t});
      }

    default:
      assert(predicate == Kind::EQUAL);
      // x & s = t
      // IC: (= (and t s) t)
      return d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::AND, {t, s}), t});
  }
}

Node
BvInverter::ic_or(Kind predicate, const Node& node, const Node& t, size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  switch (predicate)
  {
    case Kind::DISTINCT:
      // x | s != t
      // IC: (or (not s) (not t))
      {
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(Kind::NOT, {s}), d_nm.mk_node(Kind::NOT, {t})});
      }

    default:
      assert(predicate == Kind::EQUAL);
      // x | s = t
      // IC: (= (or t s) t)
      return d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::OR, {t, s}), t});
  }
}

Node
BvInverter::ic_bv_and(Kind predicate,
                      const Node& node,
                      const Node& t,
                      size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x & s <_u t
      // IC: (distinct t 0_[w])
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x & s <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x & s >_u t
      // IC: (bvult t s)
      return d_nm.mk_node(Kind::BV_ULT, {t, s});

    case Kind::BV_UGE:
      // x & s >=_u t
      // IC: (bvuge s t)
      return d_nm.mk_node(Kind::BV_UGE, {s, t});

    case Kind::BV_SLT:
      // x & s <_s t
      // IC: (bvslt (bvand (bvnot (bvneg t)) s) t)
      return d_nm.mk_node(
          Kind::BV_SLT,
          {d_nm.mk_node(
               Kind::BV_AND,
               {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {t})}),
                s}),
           t});

    case Kind::BV_SLE:
      // x & s <=_s t
      // IC: (bvuge s (bvand t min_signed_[w]))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::BV_UGE,
                            {s, d_nm.mk_node(Kind::BV_AND, {t, mins})});
      }

    case Kind::BV_SGT:
      // x & s >_s t
      // IC: (bvslt t (bvand s max_sigend_[w]))
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(Kind::BV_SLT,
                            {t, d_nm.mk_node(Kind::BV_AND, {s, maxs})});
      }

    case Kind::BV_SGE:
      // x & s >=_s t
      // IC: (or (= (bvand s t) t) (bvslt t (bvand (bvsub t s) s)))
      return d_nm.mk_node(
          Kind::OR,
          {d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_AND, {s, t}), t}),
           d_nm.mk_node(
               Kind::BV_SLT,
               {t,
                d_nm.mk_node(Kind::BV_AND,
                             {d_nm.mk_node(Kind::BV_SUB, {t, s}), s})})});

    case Kind::DISTINCT:
      // x & s != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                             d_nm.mk_node(Kind::DISTINCT, {t, zero})});
      }

    default:
      assert(predicate == Kind::EQUAL);
      // x & s = t
      // IC: (= (bvand t s) t)
      return d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_AND, {t, s}), t});
  }
}

Node
BvInverter::ic_bv_or(Kind predicate,
                     const Node& node,
                     const Node& t,
                     size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x | s <_u t
      // IC: (bvult s t)
      return d_nm.mk_node(Kind::BV_ULT, {s, t});

    case Kind::BV_ULE:
      // x | s <=_u t
      // IC: (bvuge t s)
      return d_nm.mk_node(Kind::BV_UGE, {t, s});

    case Kind::BV_UGT:
      // x | s >_u t
      // IC: (bvult t ~0_[w])
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::BV_ULT, {t, ones});
      }

    case Kind::BV_UGE:
      // x | s >=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_SLT:
      // x | s <_s t
      // IC: (bvslt (bvor (bvnot (bvsub s t)) s) t)
      return d_nm.mk_node(
          Kind::BV_SLT,
          {d_nm.mk_node(Kind::BV_OR,
                        {d_nm.mk_node(Kind::BV_NOT,
                                      {d_nm.mk_node(Kind::BV_SUB, {s, t})}),
                         s}),
           t});

    case Kind::BV_SLE:
      // x | s <=_s t
      // IC: (bvsge t (bvor s min_signed_[w]))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::BV_SGE,
                            {t, d_nm.mk_node(Kind::BV_OR, {s, mins})});
      }

    case Kind::BV_SGT:
      // x | s >_s t
      // IC: (bvslt t (bvor s max_sigend_[w]))
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(Kind::BV_SLT,
                            {t, d_nm.mk_node(Kind::BV_OR, {s, maxs})});
      }

    case Kind::BV_SGE:
      // x | s >=_s t
      // IC: (bvsge s (bvand s t))
      return d_nm.mk_node(Kind::BV_SGE,
                          {s, d_nm.mk_node(Kind::BV_AND, {s, t})});

    case Kind::DISTINCT:
      // x | s != t
      // IC: (or (distinct s ~0_[w]) (distinct t ~0_[w]))
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {s, ones}),
                             d_nm.mk_node(Kind::DISTINCT, {t, ones})});
      }

    default:
      assert(predicate == Kind::EQUAL);
      // x | s = t
      // IC: (= (bvor t s) t)
      return d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_OR, {t, s}), t});
  }
}

Node
BvInverter::ic_bv_mul(Kind predicate,
                      const Node& node,
                      const Node& t,
                      size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x * s <_u t
      // IC: (distinct t 0_[w])
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x * s <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x * s >_u t
      // IC: (bvult t (bvor (bvneg s) s))
      return d_nm.mk_node(
          Kind::BV_ULT,
          {t, d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s})});

    case Kind::BV_UGE:
      // x * s >=_u t
      // IC: (bvuge (bvor (bvneg s) s) t)
      return d_nm.mk_node(
          Kind::BV_UGE,
          {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}), t});

    case Kind::BV_SLT:
      // x * s <_s t
      // IC: (bvslt (bvand (bvnot (bvneg t)) (bvor (bvneg s) s)) t)
      return d_nm.mk_node(
          Kind::BV_SLT,
          {d_nm.mk_node(
               Kind::BV_AND,
               {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {t})}),
                d_nm.mk_node(Kind::BV_OR,
                             {d_nm.mk_node(Kind::BV_NEG, {s}), s})}),
           t});

    case Kind::BV_SLE:
      // x * s <=_s t
      // IC: (not (and (= s z) (bvslt t s)))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(
            Kind::NOT,
            {d_nm.mk_node(Kind::AND,
                          {d_nm.mk_node(Kind::EQUAL, {s, zero}),
                           d_nm.mk_node(Kind::BV_SLT, {t, s})})});
      }

    case Kind::BV_SGT:
      // x * s >_s t
      // IC: (bvslt t (bvsub t (bvor (bvor s t) (bvneg s))))  */
      return d_nm.mk_node(
          Kind::BV_SLT,
          {t,
           d_nm.mk_node(Kind::BV_SUB,
                        {t,
                         d_nm.mk_node(Kind::BV_OR,
                                      {d_nm.mk_node(Kind::BV_OR, {s, t}),
                                       d_nm.mk_node(Kind::BV_NEG, {s})})})});

    case Kind::BV_SGE:
      // x * s >=_s t
      // IC: (bvsge (bvand (bvor (bvneg s) s) max_signed_[w]) t)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {d_nm.mk_node(Kind::BV_AND,
                          {d_nm.mk_node(Kind::BV_OR,
                                        {d_nm.mk_node(Kind::BV_NEG, {s}), s}),
                           maxs}),
             t});
      }

    case Kind::DISTINCT:
      // x * s != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                             d_nm.mk_node(Kind::DISTINCT, {t, zero})});
      }

    default:
      assert(predicate == Kind::EQUAL);
      // x * s = t
      // IC: (= (bvand (bvor (bvneg s) s) t) t)
      return d_nm.mk_node(
          Kind::EQUAL,
          {d_nm.mk_node(
               Kind::BV_AND,
               {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}),
                t}),
           t});
  }
}

Node
BvInverter::ic_bv_udiv(Kind predicate,
                       const Node& node,
                       const Node& t,
                       size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT: {
      // x / s <_u t
      // IC: (and (bvult 0_[w] s) (bvult 0_[w] t))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::AND,
                            {d_nm.mk_node(Kind::BV_ULT, {zero, s}),
                             d_nm.mk_node(Kind::BV_ULT, {zero, t})});
      }
      // s / x <_u t
      // IC: (and (bvult 0_[w] (bvnot (bvand (bvneg t) s))) (bvult 0_[w] t))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(
               Kind::BV_ULT,
               {zero,
                d_nm.mk_node(
                    Kind::BV_NOT,
                    {d_nm.mk_node(Kind::BV_AND,
                                  {d_nm.mk_node(Kind::BV_NEG, {t}), s})})}),
           d_nm.mk_node(Kind::BV_ULT, {zero, t})});
    }

    case Kind::BV_ULE:
      // x / s <=_u t
      // IC: (bvuge (bvor s t) (bvnot (bvneg s)))
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_UGE,
            {d_nm.mk_node(Kind::BV_OR, {s, t}),
             d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})})});
      }
      // s / x <=_u t
      // IC: (bvult 0_[w] (bvor (bvnot s) t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(
            Kind::BV_ULT,
            {zero,
             d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NOT, {s}), t})});
      }

    case Kind::BV_UGT: {
      // x / s >_u t
      // IC: (bvugt (bvudiv ~0_[w] s) t)
      Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::BV_UGT,
                            {d_nm.mk_node(Kind::BV_UDIV, {ones, s}), t});
      }
      // s / x >_u t
      // IC: (bvult t ~0_[w])
      return d_nm.mk_node(Kind::BV_ULT, {t, ones});
    }

    case Kind::BV_UGE:
      // x / s >=_u t
      // IC: (= (bvand (bvudiv (bvmul s t) t) s) s)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(
                 Kind::BV_AND,
                 {d_nm.mk_node(Kind::BV_UDIV,
                               {d_nm.mk_node(Kind::BV_MUL, {s, t}), t}),
                  s}),
             s});
      }
      // s / x >=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_SLT: {
      // x / s <_s t
      // IC: (=> (bvsle t 0_[w]) (bvslt (bvudiv min_signed_[w] s) t))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      if (idx_x == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(
            Kind::IMPLIES,
            {d_nm.mk_node(Kind::BV_SLE, {t, zero}),
             d_nm.mk_node(Kind::BV_SLT,
                          {d_nm.mk_node(Kind::BV_UDIV, {mins, s}), t})});
      }
      // s / x <_s t
      // IC: (or (bvslt s t) (bvsge t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::BV_SLT, {s, t}),
                           d_nm.mk_node(Kind::BV_SGE, {t, zero})});
    }

    case Kind::BV_SLE:
      // x / s <=_s t
      // IC: (or
      //       (= (bvudiv (bvmul s t) s) t)
      //       (=> (bvsle t 0_[w]) (bvslt (bvudiv min_signed_[w] s) t)))
      if (idx_x == 0)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(
                 Kind::EQUAL,
                 {d_nm.mk_node(Kind::BV_UDIV,
                               {d_nm.mk_node(Kind::BV_MUL, {s, t}), s}),
                  t}),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLE, {t, zero}),
                  d_nm.mk_node(Kind::BV_SLT,
                               {d_nm.mk_node(Kind::BV_UDIV, {mins, s}), t})})});
      }
      // s / x <=_s t
      // IC: (or (bvsge t ~0_[w]) (bvsge t s))
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SGE, {t, ones}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT:
      // x / s >_s t
      // IC: (or
      //       (bvsgt (bvudiv ~0_[w] s) t)
      //       (bvsgt (bvudiv max_signed_[w] s) t))
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::OR,
            {
                d_nm.mk_node(Kind::BV_SGT,
                             {d_nm.mk_node(Kind::BV_UDIV, {ones, s}), t}),
                d_nm.mk_node(Kind::BV_SGT,
                             {d_nm.mk_node(Kind::BV_UDIV, {maxs, s}), t}),
            });
      }
      // s / x >_s t
      // IC: w > 1: (and
      //              (=> (bvsge s 0_[w]) (bvsgt s t))
      //              (=> (bvslt s 0_[w]) (bvsgt (bvlshr s (_ bv1 w)) t)))
      //     w = 1: (bvsgt s t)
      if (bw > 1)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node one  = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                           d_nm.mk_node(Kind::BV_SGT, {s, t})}),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                  d_nm.mk_node(Kind::BV_SGT,
                               {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})})});
      }
      return d_nm.mk_node(Kind::BV_SGT, {s, t});

    case Kind::BV_SGE:
      // x / s >=_s t
      // IC: (or
      //       (bvsge (bvudiv ~0_[w] s) t)
      //       (bvsge (bvudiv max_signed_[w] s) t))
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(Kind::BV_SGE,
                          {d_nm.mk_node(Kind::BV_UDIV, {ones, s}), t}),
             d_nm.mk_node(Kind::BV_SGE,
                          {d_nm.mk_node(Kind::BV_UDIV, {maxs, s}), t})});
      }
      // s / x >=_s t
      // IC: w > 1: (and
      //              (=> (bvsge s 0_[w]) (bvsge s t))
      //              (=> (bvslt s 0_[w]) (bvsge (bvlshr s (_ bv1 w)) t)))
      //     w = 1: (bvsge s t)
      if (bw > 1)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node one  = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                           d_nm.mk_node(Kind::BV_SGE, {s, t})}),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                  d_nm.mk_node(Kind::BV_SGE,
                               {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})})});
      }
      return d_nm.mk_node(Kind::BV_SGE, {s, t});

    case Kind::DISTINCT: {
      // x / s != t
      // IC: (or (distinct s 0_[w]) (distinct t ~0_[w]))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                             d_nm.mk_node(Kind::DISTINCT, {t, ones})});
      }
      // s / x != t
      // IC: w > 1: true
      //     w = 1: (= (bvand s t) 0_[w])
      if (bw > 1)
      {
        return d_nm.mk_value(true);
      }
      return d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_AND, {s, t}), zero});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x / s = t
      // IC: (= (bvudiv (bvmul s t) s) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_UDIV,
                          {d_nm.mk_node(Kind::BV_MUL, {s, t}), s}),
             t});
      }
      // s / x = t
      // IC: (= (bvudiv s (bvudiv s t)) t)
      return d_nm.mk_node(
          Kind::EQUAL,
          {d_nm.mk_node(Kind::BV_UDIV,
                        {s, d_nm.mk_node(Kind::BV_UDIV, {s, t})}),
           t});
  }
}

Node
BvInverter::ic_bv_urem(Kind predicate,
                       const Node& node,
                       const Node& t,
                       size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x mod s <_u t
      // s mod x <_u t
      // IC: (distinct t 0_[w])
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x mod s <=_u t
      // s mod x <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x mod s >_u t
      // IC: (bvult t (bvnot (bvneg s)))
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_ULT,
            {t, d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})})});
      }
      // s mod x >_u t
      // IC: (bvult t s)
      return d_nm.mk_node(Kind::BV_ULT, {t, s});

    case Kind::BV_UGE:
      // x mod s >=_u t
      // IC: (bvuge (bvnot (bvneg s)) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_UGE,
            {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})}), t});
      }
      // s mod x >=_u t
      // IC: (or (bvuge (bvand (bvsub (bvadd t t) s) s) t) (bvult t s))
      return d_nm.mk_node(
          Kind::OR,
          {
              d_nm.mk_node(
                  Kind::BV_UGE,
                  {d_nm.mk_node(
                       Kind::BV_AND,
                       {d_nm.mk_node(Kind::BV_SUB,
                                     {d_nm.mk_node(Kind::BV_ADD, {t, t}), s}),
                        s}),
                   t}),
              d_nm.mk_node(Kind::BV_ULT, {t, s}),
          });

    case Kind::BV_SLT:
      // x mod s <_s t
      // IC: (bvslt (bvnot t) (bvor (bvneg s) (bvneg t)))
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::BV_SLT,
                            {d_nm.mk_node(Kind::BV_NOT, {t}),
                             d_nm.mk_node(Kind::BV_OR,
                                          {d_nm.mk_node(Kind::BV_NEG, {s}),
                                           d_nm.mk_node(Kind::BV_NEG, {t})})});
      }
      // s mod x <_s t
      // IC: (or (bvslt s t) (bvslt 0_[w] t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {
                                d_nm.mk_node(Kind::BV_SLT, {s, t}),
                                d_nm.mk_node(Kind::BV_SLT, {zero, t}),
                            });
      }

    case Kind::BV_SLE:
      // x mod s <=_s t
      // IC: (bvslt ~0_[w] (bvand (bvneg s) t))
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::BV_SLT,
            {ones,
             d_nm.mk_node(Kind::BV_AND, {d_nm.mk_node(Kind::BV_NEG, {s}), t})});
      }
      // s mod x <=_s t
      // IC: (or (bvult t min) (bvsge t s))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_ULT, {t, mins}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT: {
      // x mod s >_s t
      // IC: (and
      //       (and
      //         (=> (bvsgt s 0_[w]) (bvslt t (bvnot (bvneg s))))
      //         (=> (bvsle s 0_[w]) (distinct t max_signed_[w])))
      //       (or (distinct t 0_[w]) (distinct s (_ bv1 w))))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      Node one  = d_nm.mk_value(BitVector::mk_one(bw));
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(
                 Kind::AND,
                 {
                     d_nm.mk_node(
                         Kind::IMPLIES,
                         {d_nm.mk_node(Kind::BV_SGT, {s, zero}),
                          d_nm.mk_node(Kind::BV_SLT,
                                       {t,
                                        d_nm.mk_node(Kind::BV_NOT,
                                                     {d_nm.mk_node(Kind::BV_NEG,
                                                                   {s})})})}),
                     d_nm.mk_node(Kind::IMPLIES,
                                  {d_nm.mk_node(Kind::BV_SLE, {s, zero}),
                                   d_nm.mk_node(Kind::DISTINCT, {t, maxs})}),
                 }),
             d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {s, one})})});
      }
      // s mod x >_s t
      // IC: (and
      //       (=> (bvsge s 0_[w]) (bvsgt s t))
      //       (=> (bvslt s 0_[w])
      //           (bvsgt (bvlshr (bvsub s (_ bv1 w)) (_ bv1 w)) t)))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                         d_nm.mk_node(Kind::BV_SGT, {s, t})}),
           d_nm.mk_node(
               Kind::IMPLIES,
               {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                d_nm.mk_node(
                    Kind::BV_SGT,
                    {d_nm.mk_node(Kind::BV_SHR,
                                  {d_nm.mk_node(Kind::BV_DEC, {s}), one}),
                     t})})});
    }

    case Kind::BV_SGE: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x mod s >=_s t
      // IC: (or (bvslt t s) (bvsge 0_[w] s))
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SLT, {t, s}),
                             d_nm.mk_node(Kind::BV_SGE, {zero, s})});
      }
      // s mod x >=_s t
      // IC: (and
      //       (=> (bvsge s 0_[w]) (bvsge s t))
      //       (=> (and (bvslt s 0_[w]) (bvsge t 0_[w])) (bvugt (bvsub s t) t)))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                         d_nm.mk_node(Kind::BV_SGE, {s, t})}),
           d_nm.mk_node(
               Kind::IMPLIES,
               {d_nm.mk_node(Kind::AND,
                             {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                              d_nm.mk_node(Kind::BV_SGE, {t, zero})}),
                d_nm.mk_node(Kind::BV_UGT,
                             {d_nm.mk_node(Kind::BV_SUB, {s, t}), t})})});
    }

    case Kind::DISTINCT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x mod s != t
      // IC: (or (distinct s (_ bv1 w)) (distinct t 0_[w]))
      if (idx_x == 0)
      {
        Node one = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(Kind::OR,
                            {
                                d_nm.mk_node(Kind::DISTINCT, {s, one}),
                                d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                            });
      }
      // s mod x != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {t, zero})});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x mod s = t
      // IC: (bvuge (bvnot (bvneg s)) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_UGE,
            {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})}), t});
      }
      // s mod x = t
      // IC: (bvuge (bvand (bvsub (bvadd t t) s) s) t)
      return d_nm.mk_node(
          Kind::BV_UGE,
          {d_nm.mk_node(Kind::BV_AND,
                        {d_nm.mk_node(Kind::BV_SUB,
                                      {d_nm.mk_node(Kind::BV_ADD, {t, t}), s}),
                         s}),
           t});
  }
}

namespace {
Node
_ic_shift_for_all_i(NodeManager& nm, Kind predicate, Kind kind, Node s, Node t)
{
  std::vector<Node> args;
  uint64_t bw = s.type().bv_size();
  for (uint64_t i = 0; i <= bw; ++i)
  {
    args.push_back(nm.mk_node(
        predicate,
        {nm.mk_node(kind, {s, nm.mk_value(BitVector::from_ui(bw, i))}), t}));
  }
  return utils::mk_nary(nm, Kind::OR, args);
}
}  // namespace

Node
BvInverter::ic_bv_shr(Kind predicate,
                      const Node& node,
                      const Node& t,
                      size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x >> s <_u t
      // s >> x <_u t
      // IC: (distinct t 0_[w])
      return d_nm.mk_node(Kind::DISTINCT, {t, zero});
    }

    case Kind::BV_ULE:
      // x >> s <=_u t
      // s >> x <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x >> s >_u t
      // IC: (bvult t (bvlshr (bvnot s) s))
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_ULT,
            {t,
             d_nm.mk_node(Kind::BV_SHR, {d_nm.mk_node(Kind::BV_NOT, {s}), s})});
      }
      // s >> x >_u t
      // IC: (bvult t s)
      return d_nm.mk_node(Kind::BV_ULT, {t, s});

    case Kind::BV_UGE:
      // x >> s >=_u t
      // IC: (= (bvlshr (bvshl t s) s) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_SHR,
                          {d_nm.mk_node(Kind::BV_SHL, {t, s}), s}),
             t});
      }
      // s >> x >=_u t
      // IC: (bvuge s t)
      return d_nm.mk_node(Kind::BV_UGE, {s, t});

    case Kind::BV_SLT:
      // x >> s <_s t
      // IC: (bvslt (bvlshr (bvnot (bvneg t)) s) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_SLT,
            {d_nm.mk_node(
                 Kind::BV_SHR,
                 {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {t})}),
                  s}),
             t});
      }
      // s >> x <_s t
      // IC: (or (bvslt s t) (bvslt 0_[w] t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SLT, {s, t}),
                             d_nm.mk_node(Kind::BV_SLT, {zero, t})});
      }

    case Kind::BV_SLE:
      // x >> s <=_s t
      // IC: (bvsge t (bvlshr t s))
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::BV_SGE,
                            {t, d_nm.mk_node(Kind::BV_SHR, {t, s})});
      }
      // s >> x <=_s t
      // IC: (or (bvult t min_signed_[w]) (bvsge t s))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_ULT, {t, mins}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT:
      // x >> s >_s t
      // IC: (bvslt t (bvlshr (bvshl max_signed_[w] s) s))
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SLT,
            {t,
             d_nm.mk_node(Kind::BV_SHR,
                          {d_nm.mk_node(Kind::BV_SHL, {maxs, s}), s})});
      }
      // s >> x >_s t
      // IC: (and
      //       (=> (bvslt s 0_[w]) (bvsgt (bvlshr s 1_[w]) t))
      //       (=> (bvsge s 0_[w]) (bvsgt s t)))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node one  = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                  d_nm.mk_node(Kind::BV_SGT,
                               {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})}),
             d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                           d_nm.mk_node(Kind::BV_SGT, {s, t})})});
      }

    case Kind::BV_SGE: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x >> s >=_s t
      // IC: (=> (not (= s 0_[w])) (bvsge (bvlshr ~0_[w] s) t))
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::IMPLIES,
            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
             d_nm.mk_node(Kind::BV_SGE,
                          {d_nm.mk_node(Kind::BV_SHR, {ones, s}), t})});
      }
      // s >> x >=_s t
      // IC: (and
      //       (=> (bvslt s 0_[w]) (bvsge (bvlshr s 1_[w]) t))
      //       (=> (bvsge s 0_[w]) (bvsge s t)))
      Node one = d_nm.mk_value(BitVector::mk_one(bw));
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(
               Kind::IMPLIES,
               {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                d_nm.mk_node(Kind::BV_SGE,
                             {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})}),
           d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                         d_nm.mk_node(Kind::BV_SGE, {s, t})})});
    }

    case Kind::DISTINCT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      Node w    = d_nm.mk_value(BitVector::from_ui(bw, bw));
      // x >> s != t
      // IC: (or (distinct t 0_[w]) (bvult s w_[w]))
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                             d_nm.mk_node(Kind::BV_ULT, {s, w})});
      }
      // s >> x != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {t, zero})});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x >> s = t
      // IC: (= (bvlshr (bvshl t s) s) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_SHR,
                          {d_nm.mk_node(Kind::BV_SHL, {t, s}), s}),
             t});
      }
      // s >> x = t
      // IC: (or (= (bvlshr s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::EQUAL, Kind::BV_SHR, s, t);
  }
}

Node
BvInverter::ic_bv_ashr(Kind predicate,
                       const Node& node,
                       const Node& t,
                       size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x >>a s <_u t
      // IC: (distinct t 0_[w])
      if (idx_x == 0)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }
      // s >>a x <_u t
      // IC: (and (or (bvult s t) (bvsge s 0_[w])) (distinct t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::BV_ULT, {s, t}),
                           d_nm.mk_node(Kind::BV_SGE, {s, zero})}),
             d_nm.mk_node(Kind::DISTINCT, {t, zero})});
      }

    case Kind::BV_ULE:
      // x >>a s <=_u t
      // IC: true
      if (idx_x == 0)
      {
        return d_nm.mk_value(true);
      }
      // s >>a x <=_u t
      // IC: (or (bvult s min_signed_[w]) (bvuge t s))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_ULT, {s, mins}),
                             d_nm.mk_node(Kind::BV_UGE, {t, s})});
      }

    case Kind::BV_UGT:
      // x >>a s >_u t
      // IC: (bvult t ~0_[w])
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::BV_ULT, {t, ones});
      }
      // s >>a x >_u t
      // IC: (or (bvslt s (bvlshr s (bvnot t))) (bvult t s))
      return d_nm.mk_node(
          Kind::OR,
          {d_nm.mk_node(Kind::BV_SLT,
                        {s,
                         d_nm.mk_node(Kind::BV_SHR,
                                      {s, d_nm.mk_node(Kind::BV_NOT, {t})})}),
           d_nm.mk_node(Kind::BV_ULT, {t, s})});

    case Kind::BV_UGE:
      // x >>a s >=_u t
      // IC: true
      if (idx_x == 0)
      {
        return d_nm.mk_value(true);
      }
      // s >>a x >=_u t
      // IC: (not (and (bvult s (bvnot s)) (bvult s t)))
      return d_nm.mk_node(
          Kind::NOT,
          {d_nm.mk_node(
              Kind::AND,
              {d_nm.mk_node(Kind::BV_ULT, {s, d_nm.mk_node(Kind::BV_NOT, {s})}),
               d_nm.mk_node(Kind::BV_ULT, {s, t})})});

    case Kind::BV_SLT:
      // x >>a s <_s t
      // IC: (bvslt (bvashr min_signed_[w] s) t)
      if (idx_x == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::BV_SLT,
                            {d_nm.mk_node(Kind::BV_ASHR, {mins, s}), t});
      }
      // s >>a x <_s t
      // IC: (or (bvslt s t) (bvslt 0_[w] t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SLT, {s, t}),
                             d_nm.mk_node(Kind::BV_SLT, {zero, t})});
      }

    case Kind::BV_SLE:
      // x >>
      // IC: (bvsge t (bvnot (bvlshr max_signed_[w] s)))
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {t,
             d_nm.mk_node(Kind::BV_NOT,
                          {d_nm.mk_node(Kind::BV_SHR, {maxs, s})})});
      }
      // s >>a x <=_s t
      // IC: (or (bvsge t 0_[w]) (bvsge t s))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SGE, {t, zero}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT: {
      Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
      // x >>a s >_s t
      // IC: (bvslt t (bvlshr max_signed_[w] s)))
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::BV_SLT,
                            {t, d_nm.mk_node(Kind::BV_SHR, {maxs, s})});
      }
      // s >>a x >_s t
      // IC: (and
      //       (bvslt t (bvand s max_signed_[w]))
      //       (bvslt t (bvor s max_signed_[w])))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::BV_SLT,
                        {t, d_nm.mk_node(Kind::BV_AND, {s, maxs})}),
           d_nm.mk_node(Kind::BV_SLT,
                        {t, d_nm.mk_node(Kind::BV_OR, {s, maxs})})});
    }

    case Kind::BV_SGE: {
      // x >>a s >=_s t
      // IC: (bvsge (bvlshr max_signed_[w] s) t)
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(Kind::BV_SGE,
                            {d_nm.mk_node(Kind::BV_SHR, {maxs, s}), t});
      }
      // s >>a x >=_s t
      // IC: (not (and (bvult t (bvnot t)) (bvslt s t)))
      return d_nm.mk_node(
          Kind::NOT,
          {d_nm.mk_node(
              Kind::AND,
              {d_nm.mk_node(Kind::BV_ULT, {t, d_nm.mk_node(Kind::BV_NOT, {t})}),
               d_nm.mk_node(Kind::BV_SLT, {s, t})})});
    }

    case Kind::DISTINCT: {
      // x >>a s != t
      // IC: true
      if (idx_x == 0)
      {
        return d_nm.mk_value(true);
      }
      // s >>a x != t
      // IC: (and
      //       (or (not (= t 0_[w])) (not (= s 0_[w])))
      //       (or (not (= t ~0_[w])) (not (= s ~0_[w]))))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {s, zero})}),
             d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {t, ones}),
                           d_nm.mk_node(Kind::DISTINCT, {s, ones})})});
      }
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x >>a s = t
      // IC: (and
      //       (=> (bvult s w_[w]) (= (bvashr (bvshl t s) s) t))
      //       (=> (bvuge s w_[w]) (or (= t ~0_[w]) (= t 0_[w])))
      //      )
      if (idx_x == 0)
      {
        Node w    = d_nm.mk_value(BitVector::from_ui(bw, bw));
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(
                 Kind::IMPLIES,
                 {
                     d_nm.mk_node(Kind::BV_ULT, {s, w}),
                     d_nm.mk_node(
                         Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_ASHR,
                                       {d_nm.mk_node(Kind::BV_SHL, {t, s}), s}),
                          t}),
                 }),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_UGE, {s, w}),
                  d_nm.mk_node(Kind::OR,
                               {d_nm.mk_node(Kind::EQUAL, {t, ones}),
                                d_nm.mk_node(Kind::EQUAL, {t, zero})})})});
      }
      // s >>a x = t
      // IC: (or (= (bvashr s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::EQUAL, Kind::BV_ASHR, s, t);
  }
}

Node
BvInverter::ic_bv_shl(Kind predicate,
                      const Node& node,
                      const Node& t,
                      size_t idx_x)
{
  const Node& s = node[1 - idx_x];
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x << s <_u t
      // s << x <_u t
      // IC: (not (= t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x << s <=_u t
      // s << x <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x << s >_u t
      // IC: (bvult t (bvshl ~0_[w] s))
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::BV_ULT,
                            {t, d_nm.mk_node(Kind::BV_SHL, {ones, s})});
      }
      // s << x >_u t
      // IC: (or (bvugt (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_UGT, Kind::BV_SHL, s, t);

    case Kind::BV_UGE:
      // x << s >=_u t
      // IC: (bvuge (bvshl ~0_[w] s) t)
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::BV_UGE,
                            {d_nm.mk_node(Kind::BV_SHL, {ones, s}), t});
      }
      // s << x >=_u t
      // IC: (or (bvuge (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_UGE, Kind::BV_SHL, s, t);

    case Kind::BV_SLT: {
      Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
      // x << s <_s t
      // IC: (bvslt (bvshl (bvlshr min_signed_[w] s) s) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_SLT,
            {d_nm.mk_node(Kind::BV_SHL,
                          {d_nm.mk_node(Kind::BV_SHR, {mins, s}), s}),
             t});
      }
      // s << x <_s t
      // IC: (bvult (bvshl min_signed_[w] s) (bvadd t min_signed_[w]))
      return d_nm.mk_node(Kind::BV_ULT,
                          {d_nm.mk_node(Kind::BV_SHL, {mins, s}),
                           d_nm.mk_node(Kind::BV_ADD, {t, mins})});
    }

    case Kind::BV_SLE: {
      Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
      // x << s <=_s t
      // IC: (bvult (bvlshr t (bvlshr t s)) min_signed_[w])
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::BV_ULT,
            {d_nm.mk_node(Kind::BV_SHR,
                          {t, d_nm.mk_node(Kind::BV_SHR, {t, s})}),
             mins});
      }
      // s << x <=_s t
      // IC: (bvult (bvlshr t s) min_signed_[w])
      return d_nm.mk_node(Kind::BV_ULT,
                          {d_nm.mk_node(Kind::BV_SHR, {t, s}), mins});
    }

    case Kind::BV_SGT:
      // x << s >_s t
      // IC: (bvslt t (bvand (bvshl max_signed_[w] s) max_signed_[w]))
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SLT,
            {t,
             d_nm.mk_node(Kind::BV_AND,
                          {d_nm.mk_node(Kind::BV_SHL, {maxs, s}), maxs})});
      }
      // s << x >_s t
      // IC: (or (bvsgt (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_SGT, Kind::BV_SHL, s, t);

    case Kind::BV_SGE:
      // x << s >=_s t
      // IC: (bvsge (bvand (bvshl max_signed_[w] s) max_signed_[w]) t)
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {d_nm.mk_node(Kind::BV_AND,
                          {d_nm.mk_node(Kind::BV_SHL, {maxs, s}), maxs}),
             t});
      }
      // s << x >=_s t
      // IC: (or (bvsge (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_SGE, Kind::BV_SHL, s, t);

    case Kind::DISTINCT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x << s != t
      // IC: (or (distinct t 0_[w]) (bvult s w_[w]))
      if (idx_x == 0)
      {
        Node w = d_nm.mk_value(BitVector::from_ui(bw, bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                             d_nm.mk_node(Kind::BV_ULT, {s, w})});
      }
      // s << x != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {t, zero})});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x << s = t
      // IC: (= (bvshl (bvlshr t s) s) t)
      if (idx_x == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_SHL,
                          {d_nm.mk_node(Kind::BV_SHR, {t, s}), s}),
             t});
      }
      // s << x = t
      // IC: (or (= (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::EQUAL, Kind::BV_SHL, s, t);
  }
}

Node
BvInverter::ic_bv_concat(Kind predicate,
                         const Node& node,
                         const Node& t,
                         size_t idx_x)
{
  const Node& x = node[idx_x];
  const Node& s = node[1 - idx_x];
  uint64_t bw_x = x.type().bv_size();
  uint64_t bw_s = s.type().bv_size();
  uint64_t bw_t = t.type().bv_size();
  Node t_x, t_s;
  if (idx_x == 0)
  {
    // t_x = t[bw(t) - 1: bw(t) - bw(x)]
    // t_s = t[bw(s) - 1: 0]
    t_x = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_t - 1, bw_t - bw_x});
    t_s = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_s - 1, 0});
  }
  else
  {
    // t_x = t[bw(x) - 1: 0]
    // t_s = t[bw(t) - 1: bw(t) - bw(s)]
    t_x = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_x - 1, 0});
    t_s = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_t - 1, bw_t - bw_s});
  }

  switch (predicate)
  {
    case Kind::BV_ULT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw_x));
      // x :: s <_u t
      // IC: (=> (= t_x 0_[bw(x)]) (bvult s t_s))
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, zero}),
                             d_nm.mk_node(Kind::BV_ULT, {s, t_s})});
      }
      // s :: x <_u t
      // IC: (and
      //       (bvule s t_s)
      //       (=> (= s t_s) (distinct t_x 0_[bw(x)]))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::BV_ULE, {s, t_s}),
           d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                         d_nm.mk_node(Kind::DISTINCT, {t_x, zero})})});
    }

    case Kind::BV_ULE:
      // x :: s <=_u t
      // IC: (=> (= t_x 0_[bw(x)]) (bvule s t_s))
      if (idx_x == 0)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, zero}),
                             d_nm.mk_node(Kind::BV_ULE, {s, t_s})});
      }
      // s :: x <=_u t
      // IC: (bvule s t_s)
      return d_nm.mk_node(Kind::BV_ULE, {s, t_s});

    case Kind::BV_UGT: {
      Node ones = d_nm.mk_value(BitVector::mk_ones(bw_x));
      // x :: s >_u t
      // IC: (=> (= t_x ~0_[bw(x)]) (bvugt s t_s))
      if (idx_x == 0)
      {
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, ones}),
                             d_nm.mk_node(Kind::BV_UGT, {s, t_s})});
      }
      // s :: x >_u t
      // IC: (and (bvuge s t_s) (=> (= s t_s) (distinct t_x ~0_[bw(x)])))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::BV_UGE, {s, t_s}),
           d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                         d_nm.mk_node(Kind::DISTINCT, {t_x, ones})})});
    }

    case Kind::BV_UGE:
      // x :: s >=_u t
      // IC: (=> (= t_x ~0_[bw(x)]) (bvuge s t_s))
      if (idx_x == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, ones}),
                             d_nm.mk_node(Kind::BV_UGE, {s, t_s})});
      }
      // s :: x >=_u t
      // IC: (bvuge s t_s)
      return d_nm.mk_node(Kind::BV_UGE, {s, t_s});

    case Kind::BV_SLT:
      // x :: s <_s t
      // IC: (=> (= t_x min_signed_[bw(x)]) (bvult s t_s))
      if (idx_x == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, mins}),
                             d_nm.mk_node(Kind::BV_ULT, {s, t_s})});
      }
      // s :: x <_s t
      // IC: (and (bvsle s t_s) (=> (= s t_s) (distinct t_x 0_[bw(x)])))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw_x));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::BV_SLE, {s, t_s}),
             d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                           d_nm.mk_node(Kind::DISTINCT, {t_x, zero})})});
      }

    case Kind::BV_SLE:
      // x :: s <=_s t
      // IC: (=> (= t_x min_signed_[bw(x)]) (bvule s t_s))
      if (idx_x == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, mins}),
                             d_nm.mk_node(Kind::BV_ULE, {s, t_s})});
      }
      // s :: x <=_s t
      // IC: (bvsle s t_s)
      return d_nm.mk_node(Kind::BV_SLE, {s, t_s});

    case Kind::BV_SGT:
      // x :: s >_s t
      // IC: (=> (= t_x max_signed_[bw(x)]) (bvugt s t_s))
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, maxs}),
                             d_nm.mk_node(Kind::BV_UGT, {s, t_s})});
      }
      // s :: x >_s t
      // IC: (and (bvsge s t_s) (=> (= s t_s) (distinct t_x ~0_[bw(x)])))
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw_x));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::BV_SGE, {s, t_s}),
             d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                           d_nm.mk_node(Kind::DISTINCT, {t_x, ones})})});
      }

    case Kind::BV_SGE:
      // x :: s >=_s t
      // IC: (=> (= t_x max_signed_[bw(x)]) (bvuge s t_s))
      if (idx_x == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, maxs}),
                             d_nm.mk_node(Kind::BV_UGE, {s, t_s})});
      }
      // s :: x >=_s t
      // IC: (bvuge s t_s)
      return d_nm.mk_node(Kind::BV_SGE, {s, t_s});

    case Kind::DISTINCT:
      // x :: s != t
      // s :: x != t
      // IC: true
      return d_nm.mk_value(true);

    default:
      assert(predicate == Kind::EQUAL);
      // x :: s = t
      // s :: x = t
      // IC: (= s t_s)
      return d_nm.mk_node(Kind::EQUAL, {s, t_s});
  }
}

Node
BvInverter::ic_bv_sext(Kind predicate,
                       const Node& node,
                       const Node& t,
                       size_t idx_x)
{
  assert(idx_x == 0);
  const Node& x = node[0];
  uint64_t bw_t = t.type().bv_size();
  uint64_t bw_x = x.type().bv_size();
  uint64_t n    = bw_t - bw_x;
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x<n> <_u t
      // IC: (distinct t 0_[w])
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw_t));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }
    case Kind::BV_UGT:
      // x<n> >_u t
      // IC: (distinct t ~0_[w])
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw_t));
        return d_nm.mk_node(Kind::DISTINCT, {t, ones});
      }

    case Kind::BV_SLT:
      // x<n> <_s t
      // IC: (bvslt ((_ sign_extend n) min_signed_[bw(x)]) t)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw_x));
        return d_nm.mk_node(
            Kind::BV_SLT, {d_nm.mk_node(Kind::BV_SIGN_EXTEND, {mins}, {n}), t});
      }
    case Kind::BV_SGT:
      // x<n> >_s t
      // IC: (bvslt t ((_ zero_extend n) max_signed_[bw(x)]))
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(
            Kind::BV_SLT, {t, d_nm.mk_node(Kind::BV_ZERO_EXTEND, {maxs}, {n})});
      }

    case Kind::BV_SLE:
      // x<n> <=_s t
      // IC: (bvsge t (bvnot ((_ zero_extend n) max_signed_[bw(x)])))
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {t,
             d_nm.mk_node(Kind::BV_NOT,
                          {d_nm.mk_node(Kind::BV_ZERO_EXTEND, {maxs}, {n})})});
      }
    case Kind::BV_SGE:
      // x<n> >=_s t
      // IC: (or
      //       (or (= ((_ extract u l) t) 0_[n + 1])
      //           (= ((_ extract u l) t) ~0_[n + 1]))
      //       (bvslt t ((_ zero_extend n) max_signed_[bw(x)])))
      //       with u = w - 1
      //            l = w - 1 - n
      {
        Node maxs  = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        Node zero  = d_nm.mk_value(BitVector::mk_zero(n + 1));
        Node ones  = d_nm.mk_value(BitVector::mk_ones(n + 1));
        uint64_t u = bw_t - 1;
        uint64_t l = bw_t - 1 - n;
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(
                 Kind::OR,
                 {d_nm.mk_node(
                      Kind::EQUAL,
                      {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), zero}),
                  d_nm.mk_node(
                      Kind::EQUAL,
                      {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), ones})}),
             d_nm.mk_node(
                 Kind::BV_SLT,
                 {t, d_nm.mk_node(Kind::BV_ZERO_EXTEND, {maxs}, {n})})});
      }

    case Kind::BV_ULE:
      // x<n> <=_u t
      // IC: true
    case Kind::BV_UGE:
      // x<n> >=_u t
      // IC: true
    case Kind::DISTINCT:
      // x<n> != t
      return d_nm.mk_value(true);

    default:
      assert(predicate == Kind::EQUAL);
      // x<n> = t
      // IC: (or
      //       (= ((_ extract u l) t) 0_[n + 1])
      //       (= ((_ extract u l) t) ~0_[n + 1]))
      //       with u = w - 1
      //            l = w - 1 - n
      {
        Node zero  = d_nm.mk_value(BitVector::mk_zero(n + 1));
        Node ones  = d_nm.mk_value(BitVector::mk_ones(n + 1));
        uint64_t u = bw_t - 1;
        uint64_t l = bw_t - 1 - n;
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), zero}),
             d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), ones

                          })});
      }
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::bv
