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
    Token d_token;
    bool d_is_bound;
    bool d_is_sort;
    uint64_t d_scope_level;
    Lexer::Coordinate d_coo;
    std::string d_name;
    bitwuzla::Term d_term;
    bitwuzla::Sort d_sort;
  };

  Node* find(const std::string& name);
  void insert(Token token, const std::string& name, uint64_t scope_level);
  void remove(Node* node);

 private:
  std::unordered_map<std::string, std::vector<Node>> d_table;
};

}  // namespace parser::smt2
}  // namespace bzla
