/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bitblast/aig/aig_printer.h"

#ifdef BZLA_USE_AIGER
#include <aiger.h>
#endif

#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <unordered_map>

#include "bitblast/aig/aig_cnf.h"

namespace bzla::bitblast::aig {

void
AigPrinter::add_output(const AigNode& output)
{
  d_outputs.push_back(output);
}

void
AigPrinter::symbol(const AigNode& n, const std::string& symbol)
{
  d_symbols.emplace(n, symbol);
}

#ifdef BZLA_USE_AIGER

namespace {

uint32_t
to_aiger_id(int64_t id)
{
  assert(id <= std::numeric_limits<int32_t>::max());
  uint32_t lit = aiger_var2lit(std::abs(id));
  if (id < 0)
  {
    return aiger_not(lit);
  }
  return lit;
}

}  // namespace

void
AigPrinter::write_aiger(const std::string& filename)
{
  aiger* aig = aiger_init();

  std::vector<AigNode> visit{d_outputs.begin(), d_outputs.end()};
  std::unordered_map<int64_t, bool> cache;

  while (!visit.empty())
  {
    auto cur = visit.back();
    auto id  = std::abs(cur.get_id());

    auto [it, inserted] = cache.emplace(id, false);
    if (inserted)
    {
      if (cur.is_and())
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
      continue;
    }
    else if (!it->second)
    {
      it->second   = true;
      auto cur_lit = to_aiger_id(id);
      if (cur.is_const())
      {
        auto its = d_symbols.find(cur);
        if (its == d_symbols.end())
        {
          aiger_add_input(aig, cur_lit, nullptr);
        }
        else
        {
          aiger_add_input(aig, cur_lit, its->second.c_str());
        }
      }
      else
      {
        assert(cur.is_and());
        auto rhs0 = to_aiger_id(cur[0].get_id());
        auto rhs1 = to_aiger_id(cur[1].get_id());
        aiger_add_and(aig, cur_lit, rhs0, rhs1);
      }
    }
    visit.pop_back();
  }

  for (const auto& output : d_outputs)
  {
    aiger_add_output(aig, to_aiger_id(output.get_id()), nullptr);
  }

  aiger_open_and_write_to_file(aig, filename.c_str());
  aiger_reset(aig);
}

#else

void
AigPrinter::write_aiger(const std::string& filename)
{
  (void) filename;
  std::cerr
      << "Bitwuzla not compiled with AIGER support. Reconfigure with --aiger."
      << std::endl;
}

#endif

class CnfPrinter : public bitblast::SatInterface
{
 public:
  CnfPrinter() = default;

  void add(int64_t lit) override
  {
    int64_t abs_lit = std::abs(lit);
    if (abs_lit > d_max_var)
    {
      d_max_var = abs_lit;
    }
    if (lit == 0)
    {
      ++d_num_clauses;
    }
    d_literals.push_back(lit);
  }

  void add_clause(const std::initializer_list<int64_t>& literals) override
  {
    for (const auto& lit : literals)
    {
      add(lit);
    }
    add(0);
  }

  bool value(int64_t lit) override
  {
    (void) lit;
    assert(false);
    return false;
  }

  void print(std::stringstream& out)
  {
    out << "p cnf " << d_max_var << " " << d_num_clauses << std::endl;
    bool new_line = true;
    for (size_t i = 0, size = d_literals.size(); i < size; ++i)
    {
      int32_t lit = d_literals[i];
      if (!new_line)
      {
        out << " ";
      }
      out << lit;
      new_line = false;
      if (lit == 0)
      {
        out << std::endl;
        new_line = true;
      }
    }
  }

 private:
  int64_t d_max_var     = 0;
  int64_t d_num_clauses = 0;
  std::vector<int64_t> d_literals;
};

void
AigPrinter::write_cnf(const std::string& filename)
{
  CnfPrinter printer;
  AigCnfEncoder enc(printer);

  for (const auto& output : d_outputs)
  {
    enc.encode(output, true);
  }

  std::stringstream ss;
  printer.print(ss);
  std::ofstream out(filename, std::ios::out);
  if (out.is_open())
  {
    out << ss.str();
  }
}

}  // namespace bzla::bitblast::aig
