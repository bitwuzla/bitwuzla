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
  struct Node
  {
    Node(Token token, const std::string& symbol, uint64_t scope_level);
    bool has_symbol() const;
    Token d_token;
    std::string d_symbol;
    uint64_t d_scope_level;
    Lexer::Coordinate d_coo;
    bitwuzla::Term d_term;
    bitwuzla::Sort d_sort;
    bool d_is_bound = false;
    Node* d_next    = nullptr;
  };

  SymbolTable();

  Node* find(const std::string& symbol) const;
  Node* insert(Token token,
               const std::string& symbol,
               uint64_t scope_level = 0);
  void remove(Node* node);
  void pop_scope(uint64_t scope_level);

  void init_array_symbols();
  void init_bv_symbols();
  void init_fp_symbols();
#ifndef NDEBUG
  void print() const;
#endif

 private:
  inline static std::array<uint32_t, 4> s_primes = {
      1000000007u, 2000000011u, 3000000019u, 4000000007u};

  struct SymbolHash
  {
    std::size_t operator()(const std::string& s) const;
  };
  struct SymbolEqual
  {
    bool operator()(const std::string& lhs, const std::string& rhs) const;
  };

  void insert(Token token);
  void init_reserved_words();
  void init_commands();
  void init_keywords();
  void init_core_symbols();

  std::unordered_map<std::string, Node*, SymbolHash, SymbolEqual> d_table;
};

}  // namespace parser::smt2
}  // namespace bzla

#endif
