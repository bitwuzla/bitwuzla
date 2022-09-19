#include "printer/printer.h"

#include <iostream>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "bitvector.h"

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
    os << "(_ BitVec " << type.get_bv_size() << ")";
  }
  else if (type.is_fp())
  {
    os << "(_ FloatingPoint " << type.get_fp_exp_size() << " "
       << type.get_fp_sig_size() << ")";
  }
  else if (type.is_rm())
  {
    os << "RoundingMode";
  }
  else if (type.is_array())
  {
    os << "(Array ";
    print(os, type.get_array_index());
    os << " ";
    print(os, type.get_array_element());
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

        case Kind::NOT:
        case Kind::AND:
        case Kind::OR:
        case Kind::FP_ABS:
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORM:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORM:
        case Kind::FP_IS_ZERO:
        case Kind::FP_NEG:
        case Kind::EQUAL:
        case Kind::BV_NOT:
        case Kind::BV_AND:
        case Kind::BV_ADD:
        case Kind::BV_MUL:
        case Kind::BV_ULT:
        case Kind::BV_SHL:
        case Kind::BV_SLT:
        case Kind::BV_SHR:
        case Kind::BV_ASHR:
        case Kind::BV_UDIV:
        case Kind::BV_UREM:
        case Kind::BV_CONCAT:
        case Kind::FP_EQUAL:
        case Kind::FP_LE:
        case Kind::FP_LT:
        case Kind::FP_MIN:
        case Kind::FP_MAX:
        case Kind::FP_SQRT:
        case Kind::FP_REM:
        case Kind::FP_RTI:
        case Kind::SELECT:
        case Kind::ITE:
        case Kind::FP_ADD:
        case Kind::FP_MUL:
        case Kind::FP_DIV:
        case Kind::STORE:
        case Kind::FP_FMA: os << "(" << info.smt2_name; break;

        case Kind::FP_TO_FP_FROM_BV:
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
        case Kind::FP_TO_FP_FROM_FP:
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV:
        case Kind::BV_EXTRACT:
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
        else
        {
          // TODO: more values
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
