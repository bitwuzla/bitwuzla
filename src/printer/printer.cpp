/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "printer/printer.h"

#include <iostream>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "backtrack/assertion_stack.h"
#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "parser/smt2/lexer.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla {

using namespace node;

/* --- Printer public ------------------------------------------------------- */

int32_t Printer::s_stream_index_maximum_depth = std::ios_base::xalloc();
int32_t Printer::s_stream_index_bv_format     = std::ios_base::xalloc();

void
Printer::print(std::ostream& os, const Node& node)
{
  size_t depth = os.iword(Printer::s_stream_index_maximum_depth);
  unordered_node_ref_map<std::string> let_map, def_map;
  bool annotate = depth && node.num_children() > 0;
  if (annotate)
  {
    os << "(!@t" << node.id() << " ";
  }
  letify(os, node, def_map, let_map, depth);
  if (annotate)
  {
    os << ")";
  }
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
  else if (type.is_uninterpreted())
  {
    const std::optional<std::string>& symbol = type.uninterpreted_symbol();
    os << (symbol ? *symbol : "@bzla.sort" + std::to_string(type.id()));
  }
  else if (type.is_fun())
  {
    const auto& types = type.fun_types();
    size_t n          = types.size();
    for (size_t i = 0; i < n - 1; ++i)
    {
      os << types[i] << " ";
    }
    os << "-> " << types[n - 1];
  }
  else
  {
    assert(false);
  }
}

void
Printer::print_formula(std::ostream& os,
                       const backtrack::AssertionView& assertions)
{
  bool has_arrays = false, has_bv = false, has_fp = false, has_funs = false;
  bool has_quants = false;
  node_ref_vector visit;
  node_ref_vector decls;
  unordered_node_ref_set cache;
  size_t level = 0;

  std::vector<Node> defs;
  std::unordered_map<Node, uint64_t> parents;
  for (size_t i = 0, n = assertions.size(); i < n; ++i)
  {
    visit.emplace_back(assertions[i]);
  }
  while (!visit.empty())
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.insert(cur);
    visit.pop_back();

    if (inserted)
    {
      Kind kind = cur.kind();
      if (kind == Kind::FORALL || kind == Kind::EXISTS || kind == Kind::LAMBDA)
      {
        continue;
      }
      else
      {
        for (const Node& c : cur)
        {
          parents[c] += 1;
          if (c.num_children() > 1 && parents[c] == 2)
          {
            defs.push_back(c);
          }
          visit.push_back(c);
        }
      }
    }
  }

  cache.clear();
  for (size_t i = 0, n = assertions.size(); i < n; ++i)
  {
    visit.emplace_back(assertions[i]);
  }
  while (!visit.empty())
  {
    const Node& cur = visit.back();
    visit.pop_back();
    Kind kind           = cur.kind();
    auto [it, inserted] = cache.insert(cur);
    if (!has_quants && (kind == Kind::EXISTS || kind == Kind::FORALL))
    {
      has_quants = true;
    }
    else if (!has_bv
             && (kind == Kind::FP_TO_SBV || kind == Kind::FP_TO_FP_FROM_UBV))
    {
      has_bv = true;
    }
    else if (!has_fp
             && (kind == Kind::FP_TO_FP_FROM_BV
                 || kind == Kind::FP_TO_FP_FROM_FP
                 || kind == Kind::FP_TO_FP_FROM_SBV
                 || kind == Kind::FP_TO_FP_FROM_UBV))
    {
      has_fp = true;
    }
    if (inserted)
    {
      if (cur.is_const() || cur.is_value())
      {
        if (!has_arrays && cur.type().is_array())
        {
          has_arrays = true;
        }
        else if (!has_bv && cur.type().is_bv())
        {
          has_bv = true;
        }
        else if (!has_fp && (cur.type().is_fp() || cur.type().is_rm()))
        {
          has_fp = true;
        }
        else if (!has_funs && (cur.type().is_fun()))
        {
          has_funs = true;
        }
        if (!cur.is_value())
        {
          decls.emplace_back(cur);
        }
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  }

  // print logic
  std::string logic;
  os << "(set-logic ";
  if (!has_quants)
  {
    logic += "QF_";
  }
  if (has_arrays)
  {
    logic += "A";
  }
  if (has_funs)
  {
    logic += "UF";
  }
  if (has_bv)
  {
    logic += "BV";
  }
  if (has_fp)
  {
    logic += "FP";
  }
  os << (logic == "QF_" ? "ALL" : logic) << ")" << std::endl;

  // print declarations
  std::sort(decls.begin(), decls.end());
  for (const Node& n : decls)
  {
    const Type& type = n.type();
    if (type.is_fun() && type.fun_arity())
    {
      os << "(declare-fun " << n << " (";
      const auto& types = type.fun_types();
      size_t n          = types.size();
      for (size_t i = 0; i < n - 1; ++i)
      {
        os << (i > 0 ? " " : "") << types[i];
      }
      os << ") " << types[n - 1] << ")" << std::endl;
    }
    else
    {
      os << "(declare-const " << n << " " << n.type() << ")" << std::endl;
    }
  }

  // print definitions
  std::sort(defs.begin(), defs.end(), [](const Node& a, const Node& b) {
    return a.id() < b.id();
  });
  node::unordered_node_ref_map<std::string> def_map;
  uint64_t ndefs = 0;
  for (const Node& node : defs)
  {
    std::string symbol = "@def" + std::to_string(ndefs);
    os << "(define-fun " << symbol << " () " << node.type() << " ";
    node::unordered_node_ref_map<std::string> let_map;
    letify(os, node, def_map, let_map, 0);
    os << ")" << std::endl;
    def_map[node] = symbol;
    ++ndefs;
  }

  // print assertions
  for (size_t i = 0, n = assertions.size(); i < n; ++i)
  {
    if (!assertions[i].is_value() || !assertions[i].value<bool>())
    {
      size_t l = assertions.level(i);
      if (l > level)
      {
        os << "(push " << (l - level) << ")" << std::endl;
        level = l;
      }
      node::unordered_node_ref_map<std::string> let_map;
      os << "(assert ";
      letify(os, assertions[i], def_map, let_map, 0);
      os << ")" << std::endl;
    }
  }

  os << "(check-sat)" << std::endl;
  os << "(exit)" << std::endl;
}

/* --- Printer private ------------------------------------------------------ */

void
Printer::print(std::ostream& os,
               const Node& node,
               node::unordered_node_ref_map<std::string>& def_map,
               node::unordered_node_ref_map<std::string>& let_map,
               size_t max_depth)
{
  // configure bit-vector output number format
  uint8_t bv_format = os.iword(Printer::s_stream_index_bv_format);
  if (!bv_format) bv_format = 2;
  assert(bv_format == 2 || bv_format == 10 || bv_format == 16);

  std::vector<std::pair<ConstNodeRef, size_t>> visit;
  visit.emplace_back(node, 0);
  node::unordered_node_ref_map<bool> cache;
  bool expect_space = false;
  do
  {
    const auto& p    = visit.back();
    const Node& cur  = p.first;
    size_t cur_depth = p.second;

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      Kind kind = cur.kind();
      if (kind == Kind::VALUE || kind == Kind::CONSTANT
          || kind == Kind::VARIABLE)
      {
        it->second = true;
        continue;
      }

      // Stop at maximum depth
      if (max_depth && cur_depth >= max_depth)
      {
        it->second = true;
        continue;
      }

      auto lit = let_map.find(cur);
      if (lit != let_map.end())
      {
        it->second = true;
        continue;
      }
      lit = def_map.find(cur);
      if (lit != def_map.end())
      {
        it->second = true;
        continue;
      }

      for (size_t i = 0, size = cur.num_children(); i < size; ++i)
      {
        visit.emplace_back(cur[size - 1 - i], cur_depth + 1);
      }

      if (expect_space)
      {
        os << " ";
      }
      expect_space = true;

      const char* symbol = KindInfo::smt2_name(cur.kind());
      switch (cur.kind())
      {
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
        case Kind::BV_DEC:
        case Kind::BV_INC:
        case Kind::BV_MUL:
        case Kind::BV_NAND:
        case Kind::BV_NEG:
        case Kind::BV_NEGO:
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
        case Kind::FP_FP:
        case Kind::FP_GEQ:
        case Kind::FP_GT:
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORMAL:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORMAL:
        case Kind::FP_IS_ZERO:
        case Kind::FP_LEQ:
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
        case Kind::STORE: os << "(" << symbol; break;

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
          os << "((_ " << symbol;
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
          os << "(" << symbol << " ((";
          print_symbol(os, cur[0]);
          os << " ";
          Printer::print(os, cur[0].type());
          os << ")) ";
          visit.pop_back();  // Pop variable
          visit.pop_back();  // Pop body
          letify(os, cur[1], def_map, let_map, max_depth);
          break;

        case Kind::VALUE:
        case Kind::CONSTANT:
        case Kind::VARIABLE:
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
      if (expect_space)
      {
        os << " ";
      }
      expect_space = true;

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
          if (bv_format == 10)
          {
            os << "(_ bv" << cur.value<BitVector>().str(bv_format) << " "
               << type.bv_size() << ")";
          }
          else
          {
            // If format is hex but bv size is not divisible by 4, we default
            // back to binary.
            uint64_t size = type.bv_size();
            if (bv_format == 16 && size % 4 == 0)
            {
              os << "#x";
              const BitVector& val = cur.value<BitVector>();
              if (val.is_zero())
              {
                os << std::string(size / 4, '0');
              }
              else
              {
                os << val.str(16);
              }
            }
            else
            {
              os << "#b" << cur.value<BitVector>().str(2);
            }
          }
        }
        else if (type.is_fp())
        {
          os << cur.value<FloatingPoint>().str(
              bv_format == 2 || bv_format == 16 ? 2 : 10);
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
      else if (max_depth && cur_depth >= max_depth)
      {
        os << "@t" << cur.id();
      }
      else
      {
        auto lit = let_map.find(cur);
        if (lit != let_map.end())
        {
          os << lit->second;
        }
        else
        {
          lit = def_map.find(cur);
          assert(lit != def_map.end());
          os << lit->second;
        }
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
    if (symbol->get().empty())
    {
      os << "||";
    }
    else if (parser::smt2::Lexer::is_valid_symbol(symbol->get())
             || parser::smt2::Lexer::is_valid_quoted_symbol(symbol->get()))
    {
      os << symbol->get();
    }
    else
    {
      if (symbol->get().find('|') != std::string::npos)
      {
        throw printer::Exception("invalid symbol '" + symbol->get()
                                 + "', symbol is not SMT-LIB compliant");
      }
      os << "|" << symbol->get() << "|";
    }
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
                node::unordered_node_ref_map<std::string>& def_map,
                node::unordered_node_ref_map<std::string>& let_map,
                size_t max_depth)
{
  node::node_ref_vector visit{node}, lets;
  std::vector<size_t> depth{0};
  node::unordered_node_ref_map<bool> cache;
  node::unordered_node_ref_map<uint64_t> refs;

  // Find nodes that need to be letified (i.e., referenced more than once)
  node::node_ref_vector binders;
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();
    size_t cur_depth = depth.back();
    depth.pop_back();

    // Do not go below binders
    auto kind = cur.kind();
    if (kind == Kind::FORALL || kind == Kind::EXISTS || kind == Kind::LAMBDA)
    {
      binders.push_back(cur);
      continue;
    }

    // Do not go below definitions
    if (def_map.find(cur) != def_map.end())
    {
      continue;
    }

    // Do not go further than the maximum specified depth.
    if (max_depth > 0 && cur_depth >= max_depth)
    {
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      for (size_t i = 0, size = cur.num_children(); i < size; ++i)
      {
        visit.push_back(cur[i]);
        depth.push_back(cur_depth + 1);
        ++refs[cur[i]];
        if (refs[cur[i]] == 2 && cur[i].num_children() > 0
            && def_map.find(cur[i]) == let_map.end())
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

  size_t nlets = lets.size();
  if (nlets > 0)
  {
    for (size_t i = 0; i < nlets; ++i)
    {
      if (i > 0)
      {
        os << " ";
      }
      os << "(let (";

      // Construct symbol of let
      std::stringstream ss;
      ss << "_let" << i;

      os << "(" << ss.str() << " ";
      print(os, lets[i], def_map, let_map, max_depth);
      os << "))";

      let_map[lets[i]] = ss.str();
    }
    os << " ";
  }

  print(os, node, def_map, let_map, max_depth);

  for (size_t i = 0; i < nlets; ++i)
  {
    os << ")";
  }
}

namespace printer {

std::ostream&
operator<<(std::ostream& ostream, const set_depth& d)
{
  ostream.iword(Printer::s_stream_index_maximum_depth) = d.depth();
  return ostream;
}

std::ostream&
operator<<(std::ostream& ostream, const set_bv_format& f)
{
  ostream.iword(Printer::s_stream_index_bv_format) = f.format();
  return ostream;
}

}  // namespace printer

}  // namespace bzla
