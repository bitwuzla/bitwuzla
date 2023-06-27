/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/aig_bitblaster.h"

#include "node/node_ref_vector.h"
#include "solver/bv/bv_solver.h"

namespace bzla::bv {

void
AigBitblaster::bitblast(const Node& t)
{
  using namespace node;

  node_ref_vector visit{t};
  do
  {
    const Node& cur = visit.back();
    assert(cur.type().is_bool() || cur.type().is_bv());

    auto it = d_bitblaster_cache.find(cur);
    if (it == d_bitblaster_cache.end())
    {
      d_bitblaster_cache.emplace(cur, bb::AigBitblaster::Bits());
      if (!BvSolver::is_leaf(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.empty())
    {
      const Type& type = cur.type();
      assert(type.is_bool() || type.is_bv());

      switch (cur.kind())
      {
        case Kind::VALUE:
          it->second = type.is_bool()
                           ? d_bitblaster.bv_value(
                               BitVector::from_ui(1, cur.value<bool>() ? 1 : 0))
                           : d_bitblaster.bv_value(cur.value<BitVector>());
          break;

        // Boolean abstractions
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORMAL:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORMAL:
        case Kind::FP_IS_ZERO:
        case Kind::FP_EQUAL:
        case Kind::FP_LEQ:
        case Kind::FP_LT:
        case Kind::FORALL:
        // Bit-vector abstractions
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
        // Both
        case Kind::SELECT:
        case Kind::APPLY:
        case Kind::CONSTANT:
          assert(BvSolver::is_leaf(cur));
          it->second = type.is_bool()
                           ? d_bitblaster.bv_constant(1)
                           : d_bitblaster.bv_constant(type.bv_size());
          break;

        case Kind::NOT:
        case Kind::BV_NOT:
          assert(cur.kind() != Kind::NOT || type.is_bool());
          assert(cur.kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_not(bits(cur[0]));
          break;

        case Kind::AND:
        case Kind::BV_AND:
          assert(cur.kind() != Kind::NOT || type.is_bool());
          assert(cur.kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_and(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::OR:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_or(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_XOR:
          it->second = d_bitblaster.bv_xor(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_EXTRACT:
          assert(type.is_bv());
          it->second =
              d_bitblaster.bv_extract(bits(cur[0]), cur.index(0), cur.index(1));
          break;

        case Kind::EQUAL: {
          const Type& type0 = cur[0].type();
          if (type0.is_bool() || type0.is_bv())
          {
            it->second = d_bitblaster.bv_eq(bits(cur[0]), bits(cur[1]));
          }
          else
          {
            // For all other cases we abstract equality as a Boolean constant.
            it->second = d_bitblaster.bv_constant(1);
          }
        }
        break;

        case Kind::BV_COMP:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_eq(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ADD:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_add(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_MUL:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_mul(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ULT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_ult(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SHL:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shl(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SLT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_slt(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shr(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ASHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_ashr(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_UDIV:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_udiv(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_UREM:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_urem(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_CONCAT:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_concat(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::ITE:
          assert(cur[0].type().is_bool());
          it->second =
              d_bitblaster.bv_ite(bits(cur[0])[0], bits(cur[1]), bits(cur[2]));
          break;

        // We should never reach other kinds.
        default: assert(false); break;
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

const bb::AigBitblaster::Bits&
AigBitblaster::bits(const Node& term) const
{
  if (d_bitblaster_cache.find(term) == d_bitblaster_cache.end())
  {
    return d_empty;
  }
  return d_bitblaster_cache.at(term);
}

uint64_t
AigBitblaster::count_aig_ands(const Node& term, AigNodeRefSet& cache)
{
  std::vector<std::reference_wrapper<const bb::AigNode>> visit;
  bitblast(term);
  const auto& b = bits(term);
  visit.insert(visit.end(), b.begin(), b.end());
  assert(!visit.empty());

  uint64_t res = 0;
  do
  {
    const bb::AigNode& cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      if (cur.is_and())
      {
        ++res;
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
    }
  } while (!visit.empty());

  return res;
}

}  // namespace bzla::bv
