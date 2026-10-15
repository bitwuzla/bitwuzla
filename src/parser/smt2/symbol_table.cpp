/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/smt2/symbol_table.h"

#include <cassert>
#include <cstring>

namespace bzla {
namespace parser::smt2 {

SymbolTable::Node::Node(Token token,
                        std::string_view symbol,
                        uint64_t assertion_level)
    : d_token(token),
      d_symbol(symbol),
      d_assertion_level(assertion_level),
      d_coo({0, 0})
{
}

SymbolTable::SymbolTable() { init(); }

SymbolTable::~SymbolTable() {}

void
SymbolTable::reset()
{
  d_entries.clear();
  d_num_entries = 0;
  init();
}

bool
SymbolTable::Node::has_symbol() const
{
  return !d_symbol.empty();
}

SymbolTable::Node*
SymbolTable::insert(Token token,
                    std::string_view symbol,
                    bool is_pending,
                    uint64_t assertion_level)
{
  Node* node = new Node(token, symbol, assertion_level);
  if (is_pending)
  {
    d_pending_symbols.push_back(node);
  }
  else
  {
    insert(node);
  }
  return node;
}

void
SymbolTable::insert(Node* node)
{
  // keep the load factor <= 1/2
  if (2 * (d_num_entries + 1) > d_entries.size())
  {
    resize(2 * d_entries.size());
  }
  std::string_view symbol = strip_pipes(node->d_symbol);
  size_t h                = hash(symbol);
  Entry& entry            = d_entries[find_entry(symbol, h)];
  if (entry.d_node)
  {
    node->d_next = std::move(entry.d_node);
  }
  else
  {
    entry.d_hash = h;
    d_num_entries += 1;
  }
  entry.d_node.reset(node);
}

void
SymbolTable::insert_pending_symbols(size_t start)
{
  assert(start <= d_pending_symbols.size());
  for (size_t i = start, n = d_pending_symbols.size(); i < n; ++i)
  {
    insert(d_pending_symbols[i]);
  }
  d_pending_symbols.resize(start);
}

void
SymbolTable::remove(Node* node)
{
  remove(node->d_symbol);
}

void
SymbolTable::remove(const std::string& symbol)
{
  std::string_view s = strip_pipes(symbol);
  size_t idx         = find_entry(s, hash(s));
  Entry& entry       = d_entries[idx];
  assert(entry.d_node);
  assert(entry.d_node->d_symbol == symbol);
  // Note: symbol may be a reference to the symbol of the removed node.
  entry.d_node = std::move(entry.d_node->d_next);
  if (!entry.d_node)
  {
    erase_entry(idx);
  }
}

void
SymbolTable::pop_level(uint64_t assertion_level)
{
  for (size_t i = 0, n = d_entries.size(); i < n; ++i)
  {
    Entry& entry = d_entries[i];
    if (!entry.d_node)
    {
      continue;
    }
    while (entry.d_node && entry.d_node->d_assertion_level >= assertion_level)
    {
      entry.d_node = std::move(entry.d_node->d_next);
    }
    if (!entry.d_node)
    {
      // Erasing may move a subsequent entry into this slot, which then
      // still needs to be processed. Entries are only moved into slots that
      // either are revisited or have not been visited yet, or entries that
      // were already processed.
      erase_entry(i);
      i -= 1;
    }
  }
}

SymbolTable::Node*
SymbolTable::find(std::string_view symbol) const
{
  symbol = strip_pipes(symbol);
  return d_entries[find_entry(symbol, hash(symbol))].d_node.get();
}

/* SymbolTable private ------------------------------------------------------ */

size_t
SymbolTable::hash(std::string_view symbol)
{
  // Process 8 bytes at a time and finalize with the 64-bit finalizer of
  // MurmurHash3 to distribute the hash value over the lower bits used for
  // indexing the table.
  const char* p = symbol.data();
  size_t n      = symbol.size();
  uint64_t h    = 0x9e3779b97f4a7c15ull ^ (n * 0xff51afd7ed558ccdull);
  for (; n >= 8; p += 8, n -= 8)
  {
    uint64_t w;
    std::memcpy(&w, p, 8);
    h = (h ^ w) * 0xbf58476d1ce4e5b9ull;
    h ^= h >> 31;
  }
  if (n > 0)
  {
    uint64_t w;
    if (n >= 4)
    {
      uint32_t lo, hi;
      std::memcpy(&lo, p, 4);
      std::memcpy(&hi, p + n - 4, 4);
      w = (static_cast<uint64_t>(hi) << 32) | lo;
    }
    else
    {
      w = (static_cast<uint64_t>(static_cast<uint8_t>(p[0])) << 16)
          | (static_cast<uint64_t>(static_cast<uint8_t>(p[n >> 1])) << 8)
          | static_cast<uint8_t>(p[n - 1]);
    }
    h = (h ^ w) * 0xbf58476d1ce4e5b9ull;
  }
  h ^= h >> 33;
  h *= 0xff51afd7ed558ccdull;
  h ^= h >> 33;
  h *= 0xc4ceb9fe1a85ec53ull;
  h ^= h >> 33;
  return h;
}

size_t
SymbolTable::find_entry(std::string_view symbol, size_t hash) const
{
  assert(d_num_entries < d_entries.size());
  size_t mask = d_entries.size() - 1;
  for (size_t i = hash & mask;; i = (i + 1) & mask)
  {
    const Entry& entry = d_entries[i];
    if (!entry.d_node
        || (entry.d_hash == hash
            && strip_pipes(entry.d_node->d_symbol) == symbol))
    {
      return i;
    }
  }
}

void
SymbolTable::erase_entry(size_t idx)
{
  assert(!d_entries[idx].d_node);
  assert(d_num_entries > 0);
  d_num_entries -= 1;
  // Backward shift deletion: move subsequent entries of the probe sequence
  // into the free slot if the free slot is between their home slot and their
  // current slot.
  size_t mask = d_entries.size() - 1;
  for (size_t i = (idx + 1) & mask; d_entries[i].d_node; i = (i + 1) & mask)
  {
    size_t home = d_entries[i].d_hash & mask;
    if (((i - home) & mask) >= ((i - idx) & mask))
    {
      d_entries[idx] = std::move(d_entries[i]);
      idx            = i;
    }
  }
}

void
SymbolTable::resize(size_t size)
{
  assert((size & (size - 1)) == 0);
  assert(size > d_num_entries);
  std::vector<Entry> entries(size);
  std::swap(entries, d_entries);
  size_t mask = size - 1;
  for (Entry& entry : entries)
  {
    if (entry.d_node)
    {
      size_t i = entry.d_hash & mask;
      while (d_entries[i].d_node)
      {
        i = (i + 1) & mask;
      }
      d_entries[i] = std::move(entry);
    }
  }
}

void
SymbolTable::init()
{
  if (d_entries.empty())
  {
    d_entries.resize(1024);
  }
  init_reserved_words();
  init_commands();
  init_keywords();
  init_core_symbols();
}

void
SymbolTable::insert(Token token)
{
  insert(token, std::to_string(token));
}

void
SymbolTable::init_reserved_words()
{
  insert(Token::BANG);
  insert(Token::UNDERSCORE);
  insert(Token::AS);
  insert(Token::BINARY_RESERVED_WORD);
  insert(Token::DECIMAL_RESERVED_WORD);
  insert(Token::EXISTS);
  insert(Token::HEXADECIMAL_RESERVED_WORD);
  insert(Token::FORALL);
  insert(Token::LET);
  insert(Token::NUMERAL_RESERVED_WORD);
  insert(Token::PAR);
  insert(Token::STRING_RESERVED_WORD);
}

void
SymbolTable::init_commands()
{
  insert(Token::ASSERT);
  insert(Token::CHECK_SAT);
  insert(Token::CHECK_SAT_ASSUMING);
  insert(Token::DECLARE_CONST);
  insert(Token::DECLARE_FUN);
  insert(Token::DECLARE_SORT);
  insert(Token::DEFINE_CONST);
  insert(Token::DEFINE_FUN);
  insert(Token::DEFINE_SORT);
  insert(Token::ECHO);
  insert(Token::EXIT);
  insert(Token::GET_ASSERTIONS);
  insert(Token::GET_ASSIGNMENT);
  insert(Token::GET_INFO);
  insert(Token::GET_INTERPOLANT);
  insert(Token::GET_INTERPOLANTS);
  insert(Token::GET_MODEL);
  insert(Token::GET_OPTION);
  insert(Token::GET_PROOF);
  insert(Token::GET_UNSAT_ASSUMPTIONS);
  insert(Token::GET_UNSAT_CORE);
  insert(Token::GET_VALUE);
  insert(Token::POP);
  insert(Token::PUSH);
  insert(Token::RESET);
  insert(Token::RESET_ASSERTIONS);
  insert(Token::SET_INFO);
  insert(Token::SET_LOGIC);
  insert(Token::SET_OPTION);
}

void
SymbolTable::init_keywords()
{
  insert(Token::ALL_STATISTICS);
  insert(Token::AUTHORS);
  insert(Token::ASSERTION_STACK_LEVELS);
  insert(Token::CATEGORY);
  insert(Token::CHAINABLE);
  insert(Token::DEFINITION);
  insert(Token::DIAG_OUTPUT_CHANNEL);
  insert(Token::ERROR_BEHAVIOR);
  insert(Token::EXTENSIONS);
  insert(Token::FUNS);
  insert(Token::FUNS_DESCRIPTION);
  insert(Token::GLOBAL_DECLARATIONS);
  insert(Token::INTERACTIVE_MODE);
  insert(Token::LANGUAGE);
  insert(Token::LEFT_ASSOC);
  insert(Token::LICENSE);
  insert(Token::NAME);
  insert(Token::NAMED);
  insert(Token::NOTES);
  insert(Token::PATTERN);
  insert(Token::PRINT_SUCCESS);
  insert(Token::PRODUCE_ASSIGNMENTS);
  insert(Token::PRODUCE_MODELS);
  insert(Token::PRODUCE_PROOFS);
  insert(Token::PRODUCE_UNSAT_ASSUMPTIONS);
  insert(Token::PRODUCE_UNSAT_CORES);
  insert(Token::RANDOM_SEED);
  insert(Token::REASON_UNKNOWN);
  insert(Token::REGULAR_OUTPUT_CHANNEL);
  insert(Token::REPR_RESOURCE_LIMIT);
  insert(Token::RIGHT_ASSOC);
  insert(Token::SMTLIB_VERSION);
  insert(Token::SORTS);
  insert(Token::SORTS_DESCRIPTION);
  insert(Token::SOURCE);
  insert(Token::STATUS);
  insert(Token::THEORIES);
  insert(Token::VALUES);
  insert(Token::VERBOSITY);
  insert(Token::VERSION);
}

void
SymbolTable::init_core_symbols()
{
  insert(Token::AND);
  insert(Token::BOOL);
  insert(Token::DISTINCT);
  insert(Token::EQUAL);
  insert(Token::FALSE);
  insert(Token::IMPLIES);
  insert(Token::ITE);
  insert(Token::NOT);
  insert(Token::OR);
  insert(Token::TRUE);
  insert(Token::XOR);
}

void
SymbolTable::init_array_symbols()
{
  insert(Token::ARRAY);
  insert(Token::ARRAY_SELECT);
  insert(Token::ARRAY_STORE);
}

void
SymbolTable::init_bv_symbols()
{
  insert(Token::BV_BITVEC);
  insert(Token::BV_ADD);
  insert(Token::BV_AND);
  insert(Token::BV_ASHR);
  insert(Token::BV_COMP);
  insert(Token::BV_CONCAT);
  insert(Token::BV_EXTRACT);
  insert(Token::BV_LSHR);
  insert(Token::BV_MUL);
  insert(Token::BV_NAND);
  insert(Token::BV_NEG);
  insert(Token::BV_NOR);
  insert(Token::BV_NOT);
  insert(Token::BV_OR);
  insert(Token::BV_REPEAT);
  insert(Token::BV_ROL);
  insert(Token::BV_ROR);
  insert(Token::BV_ROTATE_LEFT);
  insert(Token::BV_ROTATE_RIGHT);
  insert(Token::BV_SDIV);
  insert(Token::BV_SGE);
  insert(Token::BV_SGT);
  insert(Token::BV_SHL);
  insert(Token::BV_SIGN_EXTEND);
  insert(Token::BV_SLE);
  insert(Token::BV_SLT);
  insert(Token::BV_SMOD);
  insert(Token::BV_SREM);
  insert(Token::BV_SUB);
  insert(Token::BV_UDIV);
  insert(Token::BV_UGE);
  insert(Token::BV_UGT);
  insert(Token::BV_ULE);
  insert(Token::BV_ULT);
  insert(Token::BV_UREM);
  insert(Token::BV_XNOR);
  insert(Token::BV_XOR);
  insert(Token::BV_ZERO_EXTEND);
  insert(Token::BV_DEC);
  insert(Token::BV_INC);
  insert(Token::BV_REDOR);
  insert(Token::BV_REDAND);
  insert(Token::BV_REDXOR);
  insert(Token::BV_NEGO);
  insert(Token::BV_SADDO);
  insert(Token::BV_UADDO);
  insert(Token::BV_SDIVO);
  insert(Token::BV_SMULO);
  insert(Token::BV_UMULO);
  insert(Token::BV_SSUBO);
  insert(Token::BV_USUBO);
}

void
SymbolTable::init_fp_symbols()
{
  insert(Token::FP_FLOATINGPOINT);
  insert(Token::FP_FLOAT16);
  insert(Token::FP_FLOAT32);
  insert(Token::FP_FLOAT64);
  insert(Token::FP_FLOAT128);
  insert(Token::FP_ROUNDINGMODE);
  insert(Token::FP_RM_RNA);
  insert(Token::FP_RM_RNA_LONG);
  insert(Token::FP_RM_RNE);
  insert(Token::FP_RM_RNE_LONG);
  insert(Token::FP_RM_RTN);
  insert(Token::FP_RM_RTN_LONG);
  insert(Token::FP_RM_RTP);
  insert(Token::FP_RM_RTP_LONG);
  insert(Token::FP_RM_RTZ);
  insert(Token::FP_RM_RTZ_LONG);
  insert(Token::FP_ABS);
  insert(Token::FP_ADD);
  insert(Token::FP_DIV);
  insert(Token::FP_EQ);
  insert(Token::FP_FMA);
  insert(Token::FP_FP);
  insert(Token::FP_GEQ);
  insert(Token::FP_GT);
  insert(Token::FP_IS_INF);
  insert(Token::FP_IS_NAN);
  insert(Token::FP_IS_NEG);
  insert(Token::FP_IS_NORMAL);
  insert(Token::FP_IS_POS);
  insert(Token::FP_IS_SUBNORMAL);
  insert(Token::FP_IS_ZERO);
  insert(Token::FP_LEQ);
  insert(Token::FP_LT);
  insert(Token::FP_MAX);
  insert(Token::FP_MIN);
  insert(Token::FP_MUL);
  insert(Token::FP_NOTANUMBER);
  insert(Token::FP_NEG);
  insert(Token::FP_NEG_INF);
  insert(Token::FP_NEG_ZERO);
  insert(Token::FP_POS_INF);
  insert(Token::FP_POS_ZERO);
  insert(Token::FP_REM);
  insert(Token::FP_RTI);
  insert(Token::FP_SQRT);
  insert(Token::FP_SUB);
  insert(Token::FP_TO_FP);
  insert(Token::FP_TO_FP_UNSIGNED);
  insert(Token::FP_TO_SBV);
  insert(Token::FP_TO_UBV);
  insert(Token::REAL_DIV);
}

#ifndef NDEBUG
void
SymbolTable::print() const
{
  std::cout << "SymbolTable: " << std::endl;
  for (const Entry& entry : d_entries)
  {
    if (!entry.d_node)
    {
      continue;
    }
    std::cout << "'" << entry.d_node->d_symbol << "': ";
    for (Node* n = entry.d_node.get(); n; n = n->d_next.get())
    {
      std::cout << " (" << n->d_symbol << ", " << n->d_assertion_level << ")";
    }
    std::cout << std::endl;
  }
}
void
SymbolTable::print(const std::string& symbol) const
{
  std::cout << "SymbolTable: ";
  Node* node = find(symbol);
  if (!node)
  {
    std::cout << "no entry for '" << symbol << "'" << std::endl;
  }
  else
  {
    std::cout << "'" << symbol << "': ";
    for (Node* n = node; n; n = n->d_next.get())
    {
      std::cout << " (" << n->d_symbol << ", " << n->d_assertion_level << ")";
    }
    std::cout << std::endl;
  }
}
#endif

void
SymbolTable::clear_pending_symbols()
{
  for (Node* symbol : d_pending_symbols)
  {
    delete symbol;
  }
}

}  // namespace parser::smt2
}  // namespace bzla
