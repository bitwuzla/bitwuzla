#ifndef BZLA_PARSER_SMT2_SYMBOL_TABLE_H_INCLUDED
#define BZLA_PARSER_SMT2_SYMBOL_TABLE_H_INCLUDED

#include "bitwuzla/cpp/bitwuzla.h"
#include "parser/smt2/lexer.h"

namespace bzla {
namespace parser::smt2 {

class SymbolTable
{
 public:
  struct Node
  {
    Node(Token token, const std::string& name, uint64_t scope_level);
    bool has_symbol() const;
    Token d_token;
    bool d_is_bound;
    bool d_is_sort;
    uint64_t d_scope_level;
    Lexer::Coordinate d_coo;
    std::string d_symbol;
    bitwuzla::Term d_term;
    bitwuzla::Sort d_sort;
  };

  Node* find(const std::string& symbol) const;
  Node* insert(Token token,
               const std::string& symbol,
               uint64_t scope_level = 0);
  void remove(Node* node);
  void pop_scope(uint64_t scope_level);

  void init_array_symbols();
  void init_bv_symbols();
  void init_fp_symbols();

 private:
  Node* insert(Token token);
  void init_reserved_words();
  void init_commands();
  void init_keywords();
  void init_core_symbols();

  std::unordered_map<std::string, std::vector<std::unique_ptr<Node>>> d_table;
};

}  // namespace parser::smt2
}  // namespace bzla

#endif
