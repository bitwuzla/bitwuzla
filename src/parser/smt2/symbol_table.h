/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_SMT2_SYMBOL_TABLE_H_INCLUDED
#define BZLA_PARSER_SMT2_SYMBOL_TABLE_H_INCLUDED

#include <array>

#include "bitwuzla/cpp/bitwuzla.h"
#include "parser/smt2/lexer.h"

namespace bzla {
namespace parser::smt2 {

class SymbolTable
{
 public:
  /** A node in the symbol table. */
  struct Node
  {
    /**
     * Constructor.
     * @param token The token (kind) of the symbol.
     * @param symbol The string representation of the symbol.
     * @param assertion_level The assertion level (push/pop) of the symbol.
     */
    Node(Token token, const std::string& symbol, uint64_t assertion_level);
    /** @return True if the symbol is non-empty() (for dbg purposes). */
    bool has_symbol() const;
    /** The token of the symbol. Serves as a kind. */
    Token d_token;
    /** The string representation of the symbol. */
    std::string d_symbol;
    /** The assertion level of the symbol. */
    uint64_t d_assertion_level;
    /** The coordinate (in the input file) of the symbol. */
    Lexer::Coordinate d_coo;
    /**
     * The term representation of the symbol (symbol can be either term or
     * sort but not both).
     */
    bitwuzla::Term d_term;
    /**
     * The sort representation of the symbol (symbol can be either term or
     * sort but not both).
     */
    bitwuzla::Sort d_sort;
    /** True if symbol is already bound. */
    bool d_is_bound = false;
    /**
     * The next node in the shadow chain. First node is current declaration of
     * symbol, next is the declaration it shadows.
     */
    std::unique_ptr<Node> d_next = nullptr;
  };

  /** Constructor. */
  SymbolTable();
  /** Destructor. */
  ~SymbolTable();

  /** Disallow copy constructor and copy assignment . */
  SymbolTable(const SymbolTable&)    = delete;
  void operator=(const SymbolTable&) = delete;

  /** Reset symbol table. */
  void reset();

  /**
   * Find a given symbol in the symbol table.
   * Piped symbols are considered equal to their non-pided version, i.e.,
   * "|a|" and "a" refer to the same symbol.
   * @return The symbol node, if found, else nullptr. If symbol is shadowed,
   *         the most recent declaration of the symbol is returned.
   */
  Node* find(const std::string& symbol) const;
  /**
   * Insert a new symbol.
   * If the symbol already exists, it will shadow a previous declaration.
   * @param token The token of the symbol.
   * @param symbol The string representation of the symbol.
   * @param assertion_level The assertion level of the symbol.
   */
  Node* insert(Token token,
               const std::string& symbol,
               uint64_t assertion_level = 0);
  /**
   * Insert a symbol table node that was not created via the above insert().
   * The symbol table takes ownership of the node, thus the node must be
   * created via operator `new`.
   * If the symbol already exists, it will shadow a previous declaration.
   * @param node The node.
   */
  void insert(Node* node);
  /**
   * Remove a symbol node from the symbol table.
   * If the symbol is shadowed, this only removes the most recent declaration
   * of the symbol.
   * Asserts that the symbol node exists.
   * @param node The symbol node.
   */
  void remove(Node* node);
  /**
   * Remove the current declaration of the given  symbol from the symbol table.
   * If the symbol is shadowed, this only removes the most recent declaration
   * of the symbol.
   * @param symbol The symbol.
   */
  void remove(const std::string& symbol);
  /**
   * Remove all nodes from all levels down to (and including) the given
   * assertion level.
   * @param assertion_level The assertion level.
   */
  void pop_level(uint64_t assertion_level);

  /** Add array theory symbols to table. */
  void init_array_symbols();
  /** Add bit-vector theory symbols to table. */
  void init_bv_symbols();
  /** Add floating-point theory symbols to table. */
  void init_fp_symbols();
#ifndef NDEBUG
  /** Print table (for dbg purposes). */
  void print() const;
#endif

 private:
  /** Primes for hashing of symbol strings. */
  inline static std::array<uint32_t, 4> s_primes = {
      1000000007u, 2000000011u, 3000000019u, 4000000007u};
  /**
   * The hash function for symbol strings.
   * Considers piped symbols and their non-piped variants as equal.
   */
  struct SymbolHash
  {
    std::size_t operator()(const std::string& s) const;
  };
  /**
   * The comparator for symbol strings.
   * Considers piped symbols and their non-piped variants as equal.
   */
  struct SymbolEqual
  {
    bool operator()(const std::string& lhs, const std::string& rhs) const;
  };

  /** Initialize symbol table (insert reserved symbols). */
  void init();

  /** Insert symbol node for given token. */
  void insert(Token token);
  /** Add reserved word symbols to table. */
  void init_reserved_words();
  /** Add command symbols to table. */
  void init_commands();
  /** Add keyword symbols to table. */
  void init_keywords();
  /** Add core theory symbols to table. */
  void init_core_symbols();

  /**
   * The symbol table. Maps the string representation of the symbol to a
   * symbol node (chain). Shadowed symbols are represented as a node chain,
   * where the first node is the currently declared symbol, and a shadowed
   * symbol is linked via Node::d_next.
   */
  std::
      unordered_map<std::string, std::unique_ptr<Node>, SymbolHash, SymbolEqual>
          d_table;
};

}  // namespace parser::smt2
}  // namespace bzla

#endif
