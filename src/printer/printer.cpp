#include "printer/printer.h"

#include <iostream>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "bitvector.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla {

using namespace node;

using NodeRefVector = std::vector<std::reference_wrapper<const Node>>;
template <class T>
using NodeRefMap =
    std::unordered_map<std::reference_wrapper<const Node>, T, std::hash<Node>>;

/* --- Printer public ------------------------------------------------------- */

void
Printer::print(std::ostream& os, const Node& node)
{
  NodeRefMap<std::string> let_map;
  letify(os, node, let_map);
}

void
Printer::print(std::ostream& os, const Type& type)
{
  if (type.is_bool())
  {
    os << "Bool";
  }
  else if (type.is_bv())
  {
    os << "(_ BitVec " << type.bv_size() << ")";
  }
  else if (type.is_fp())
  {
    os << "(_ FloatingPoint " << type.fp_exp_size() << " " << type.fp_sig_size()
       << ")";
  }
  else if (type.is_rm())
  {
    os << "RoundingMode";
  }
  else if (type.is_array())
  {
    os << "(Array ";
    print(os, type.array_index());
    os << " ";
    print(os, type.array_element());
    os << ")";
  }
  else
  {
    assert(false);
  }
}

/* --- Printer private ------------------------------------------------------ */

void
Printer::print(std::ostream& os,
               const Node& node,
               NodeRefMap<std::string>& let_map)
{
  NodeRefVector visit{node};
  NodeRefMap<bool> cache;
  bool expect_space = false;
  do
  {
    const Node& cur = visit.back();

    auto lit = let_map.find(cur);
    if (lit != let_map.end())
    {
      if (expect_space)
      {
        os << " ";
      }
      os << lit->second;
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      if (expect_space)
      {
        os << " ";
      }

      for (size_t i = 0, size = cur.num_children(); i < size; ++i)
      {
        visit.push_back(cur[size - 1 - i]);
      }

      expect_space                = true;
      const KindInformation& info = s_node_kind_info[cur.kind()];
      switch (cur.kind())
      {
        case Kind::VALUE:
        case Kind::CONSTANT:
        case Kind::VARIABLE: it->second = true; break;

        case Kind::CONST_ARRAY:
          os << "((as const ";
          Printer::print(os, cur.type());
          os << ")";
          break;

        case Kind::NOT:
        case Kind::AND:
        case Kind::OR:
        case Kind::IMPLIES:
        case Kind::XOR:
        case Kind::DISTINCT:
        case Kind::EQUAL:
        case Kind::ITE:
        case Kind::BV_ADD:
        case Kind::BV_AND:
        case Kind::BV_ASHR:
        case Kind::BV_COMP:
        case Kind::BV_CONCAT:
        case Kind::BV_MUL:
        case Kind::BV_NAND:
        case Kind::BV_NEG:
        case Kind::BV_NOR:
        case Kind::BV_NOT:
        case Kind::BV_OR:
        case Kind::BV_REDAND:
        case Kind::BV_REDOR:
        case Kind::BV_REDXOR:
        case Kind::BV_ROL:
        case Kind::BV_ROR:
        case Kind::BV_SADDO:
        case Kind::BV_SDIV:
        case Kind::BV_SDIVO:
        case Kind::BV_SGE:
        case Kind::BV_SGT:
        case Kind::BV_SHL:
        case Kind::BV_SHR:
        case Kind::BV_SLE:
        case Kind::BV_SLT:
        case Kind::BV_SMOD:
        case Kind::BV_SMULO:
        case Kind::BV_SREM:
        case Kind::BV_SSUBO:
        case Kind::BV_SUB:
        case Kind::BV_UADDO:
        case Kind::BV_UDIV:
        case Kind::BV_UGE:
        case Kind::BV_UGT:
        case Kind::BV_ULE:
        case Kind::BV_ULT:
        case Kind::BV_UMULO:
        case Kind::BV_UREM:
        case Kind::BV_USUBO:
        case Kind::BV_XNOR:
        case Kind::BV_XOR:
        case Kind::FP_ABS:
        case Kind::FP_ADD:
        case Kind::FP_DIV:
        case Kind::FP_EQUAL:
        case Kind::FP_FMA:
        case Kind::FP_GE:
        case Kind::FP_GT:
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORM:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORM:
        case Kind::FP_IS_ZERO:
        case Kind::FP_LE:
        case Kind::FP_LT:
        case Kind::FP_MAX:
        case Kind::FP_MIN:
        case Kind::FP_MUL:
        case Kind::FP_NEG:
        case Kind::FP_REM:
        case Kind::FP_RTI:
        case Kind::FP_SQRT:
        case Kind::FP_SUB:
        case Kind::SELECT:
        case Kind::STORE: os << "(" << info.smt2_name; break;

        case Kind::BV_EXTRACT:
        case Kind::BV_REPEAT:
        case Kind::BV_ROLI:
        case Kind::BV_RORI:
        case Kind::BV_SIGN_EXTEND:
        case Kind::BV_ZERO_EXTEND:
        case Kind::FP_TO_FP_FROM_BV:
        case Kind::FP_TO_FP_FROM_FP:
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV:
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
          os << "((_ " << info.smt2_name;
          for (size_t i = 0; i < cur.num_indices(); ++i)
          {
            os << " " << cur.index(i);
          }
          os << ")";
          break;

        case Kind::APPLY:
          os << "(";
          expect_space = false;
          break;

        case Kind::EXISTS:
        case Kind::FORALL:
        case Kind::LAMBDA:
          os << "(" << info.smt2_name << " ((";
          print_symbol(os, cur[0]);
          os << " ";
          Printer::print(os, cur[0].type());
          os << ")) ";
          visit.pop_back();  // Pop variable
          visit.pop_back();  // Pop body
          letify(os, cur[1], let_map);
          break;

        case Kind::NULL_NODE:
        case Kind::NUM_KINDS: assert(false); break;
      }
      continue;
    }
    else if (!it->second)
    {
      os << ")";
      it->second = true;
    }
    else
    {
      const Type& type = cur.type();
      auto kind        = cur.kind();
      if (kind == Kind::VALUE)
      {
        if (type.is_bool())
        {
          os << (cur.value<bool>() ? "true" : "false");
        }
        else if (type.is_bv())
        {
          os << "#b" << cur.value<BitVector>();
        }
        else if (type.is_fp())
        {
          os << cur.value<FloatingPoint>();
        }
        else if (type.is_rm())
        {
          os << cur.value<RoundingMode>();
        }
        else
        {
          assert(false);
        }
      }
      else if (kind == Kind::CONSTANT || kind == Kind::VARIABLE)
      {
        print_symbol(os, cur);
      }
      else
      {
        assert(false);
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

void
Printer::print_symbol(std::ostream& os, const Node& node)
{
  const auto symbol = node.symbol();
  if (symbol)
  {
    os << symbol->get();
  }
  // Default symbol
  else
  {
    os << (node.kind() == Kind::CONSTANT ? "@bzla.const" : "@bzla.var");
    os << "_" << node.id();
  }
}

void
Printer::letify(std::ostream& os,
                const Node& node,
                NodeRefMap<std::string>& let_map)
{
  NodeRefVector visit{node}, lets;
  NodeRefMap<bool> cache;
  NodeRefMap<uint64_t> refs;

  // Find nodes that need to be letified (i.e., referenced more than once)
  NodeRefVector binders;
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    // Do not go below binders
    auto kind = cur.kind();
    if (kind == Kind::FORALL || kind == Kind::EXISTS || kind == Kind::LAMBDA)
    {
      binders.push_back(cur);
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      for (size_t i = 0, size = cur.num_children(); i < size; ++i)
      {
        visit.push_back(cur[i]);
        ++refs[cur[i]];
        if (refs[cur[i]] == 2 && cur[i].num_children() > 0)
        {
          lets.push_back(cur[i]);
        }
      }
    }
  } while (!visit.empty());

  while (!binders.empty())
  {
    const Node& cur = binders.back();
    binders.pop_back();

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      for (size_t i = 0, size = cur.num_children(); i < size; ++i)
      {
        binders.push_back(cur[i]);
        auto itr = refs.find(cur[i]);
        if (itr == refs.end())
        {
          continue;
        }
        ++itr->second;
        if (itr->second == 2 && cur[i].num_children() > 0)
        {
          lets.push_back(cur[i]);
        }
      }
    }
  }

  // Sort letified nodes by id in ascending order
  std::sort(lets.begin(), lets.end(), [](const Node& a, const Node& b) {
    return a.id() < b.id();
  });
  if (lets.size() > 0)
  {
    os << "(let (";
    for (size_t i = 0; i < lets.size(); ++i)
    {
      if (i > 0)
      {
        os << " ";
      }

      // Construct symbol of let
      std::stringstream ss;
      ss << "_let" << i;

      os << "(" << ss.str() << " ";
      print(os, lets[i], let_map);
      os << ")";

      let_map[lets[i]] = ss.str();
    }
    os << ") ";
  }

  print(os, node, let_map);

  if (lets.size() > 0)
  {
    os << ")";
  }
}

}  // namespace bzla
