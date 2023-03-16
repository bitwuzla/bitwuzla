#ifndef BZLA_PARSER_SMT2_PARSER_H_INCLUDED
#define BZLA_PARSER_SMT2_PARSER_H_INCLUDED

#include <fstream>

#include "parser/smt2/lexer.h"
#include "parser/smt2/symbol_table.h"
#include "util/logger.h"
#include "util/statistics.h"

namespace bitwuzla {
class Bitwuzla;
}

namespace bzla {
namespace parser::smt2 {

class Parser
{
 public:
  Parser(bitwuzla::Options& options, const std::string& infile_name);

  std::string parse();

  void configure_terminator(bitwuzla::Terminator* terminator);

 private:
  struct ParsedItem
  {
    ParsedItem() {}

    ParsedItem(Token token, const Lexer::Coordinate& coo)
        : d_token(token), d_coo(coo)
    {
    }

    template <typename T>
    ParsedItem(Token token, T item, const Lexer::Coordinate& coo)
        : d_token(token), d_coo(coo), d_item(item)
    {
    }

    Token d_token;
    Lexer::Coordinate d_coo;
    std::variant<SymbolTable::Node*,
                 bitwuzla::Sort,
                 bitwuzla::Term,
                 uint64_t,
                 std::string,
                 std::array<std::string, 2>>
        d_item;
  };

  void init_logic()
  {
    if (d_logic.empty())
    {
      enable_theory("ALL");
    }
  }
  void init_bitwuzla()
  {
    if (!d_bitwuzla)
    {
      d_bitwuzla.reset(new bitwuzla::Bitwuzla(d_options));
    }
  }

  bool terminate()
  {
    return d_terminator != nullptr && d_terminator->terminate();
  }

  Token next_token();

  bool parse_command();
  bool parse_command_assert();
  bool parse_command_check_sat(bool with_assumptions = false);
  bool parse_command_declare_sort();
  bool parse_command_declare_fun(bool is_const = false);
  bool parse_command_define_fun();
  bool parse_command_define_sort();
  bool parse_command_echo();
  bool parse_command_exit();
  bool parse_command_get_model();
  bool parse_command_get_unsat_assumptions();
  bool parse_command_get_unsat_core();
  bool parse_command_get_value();
  bool parse_command_pop();
  bool parse_command_push();
  bool parse_command_set_info();
  bool parse_command_set_logic();
  bool parse_command_set_option();

  bool parse_lpars(uint64_t nlpars);
  bool parse_rpars(uint64_t nrpars);

  bool parse_uint64();

  bool parse_symbol(const std::string& error_msg,
                    bool shadow     = false,
                    bool look_ahead = false,
                    Token la_char   = Token::INVALID);

  bool parse_term(bool look_ahead = false, Token la_char = Token::INVALID);
  bool parse_term_list(std::vector<std::string>* repr = nullptr);
  bool parse_open_term(Token token);
  bool parse_open_term_as();
  bool parse_open_term_indexed();
  bool parse_open_term_quant();
  bool parse_open_term_symbol();

  bool parse_sort(bitwuzla::Sort& sort,
                  bool look_ahead = false,
                  Token la_char   = Token::INVALID);
  bool parse_sort_array(bitwuzla::Sort& sort);
  bool parse_sort_bv_fp(bitwuzla::Sort& sort);

  bool close_term();
  bool close_term_as(ParsedItem& item_open);
  bool close_term_bang(ParsedItem& item_open);
  bool close_term_core(ParsedItem& item_open);
  bool close_term_array(ParsedItem& item_open);
  bool close_term_bv(ParsedItem& item_open);
  bool close_term_fp(ParsedItem& item_open);
  bool close_term_fun_app(ParsedItem& item_open);
  bool close_term_let(ParsedItem& item_open);
  bool close_term_letbind(ParsedItem& item_open);
  bool close_term_parletbind(ParsedItem& item_open);
  bool close_term_quant(ParsedItem& item_open);
  bool close_term_sorted_var(ParsedItem& item_open);
  bool close_term_sorted_vars(ParsedItem& item_open);

  void open_term_scope();
  void close_term_scope(const bitwuzla::Term& term = bitwuzla::Term());

  bool skip_sexprs(uint64_t nopen = 0);

  bool error(const std::string& error_msg,
             const Lexer::Coordinate& coo = {0, 0});
  bool error_arg(const std::string& error_msg);
  bool error_invalid();
  bool error_eof();

  bool check_token(Token token)
  {
    if (token == Token::ENDOFFILE)
    {
      return error_eof();
    }
    if (token == Token::INVALID)
    {
      return error_invalid();
    }
    return true;
  }

  bool is_symbol(Token token) const
  {
    return token == Token::SYMBOL || token == Token::ATTRIBUTE
           || (static_cast<uint32_t>(token) & d_token_class_mask) > 0;
  }

  size_t enable_theory(const std::string& logic,
                       const std::string& theory = "",
                       size_t size_prefix        = 0);
  bool is_supported_logic(const std::string& logic);

  void print_success();

  size_t nargs() const
  {
    assert(idx_open() < d_work.size());
    return d_work.size() - idx_open() - 1;
  }

  size_t nopen() const { return d_work_control.size() - 1; }

  size_t idx_open() const { return d_work_control.back(); }

  ParsedItem& item_open()
  {
    assert(idx_open() < d_work.size());
    return d_work[idx_open()];
  }

  const Lexer::Coordinate& arg_coo(size_t idx) const;

  ParsedItem& push_item(Token token, const Lexer::Coordinate& coo)
  {
    if (peek_item_is_token(Token::OPEN))
    {
      set_item(d_work.back(), token, coo);
    }
    else
    {
      d_work.emplace_back(token, coo);
    }
    return d_work.back();
  }
  template <typename T>
  ParsedItem& push_item(Token token, T item, const Lexer::Coordinate& coo)
  {
    if (peek_item_is_token(Token::OPEN))
    {
      set_item(d_work.back(), token, item, &coo);
    }
    else
    {
      d_work.emplace_back(token, item, coo);
    }
    return d_work.back();
  }

  bool peek_item_is_token(Token token) const
  {
    return d_work.size() && d_work.back().d_token == token;
  }
  bool peek_item_is_token(Token token, size_t idx) const
  {
    return idx < d_work.size() && d_work[idx].d_token == token;
  }

  void set_item(ParsedItem& item, Token token, const Lexer::Coordinate& coo)
  {
    item.d_token = token;
    item.d_coo   = coo;
  }
  template <typename T>
  void set_item(ParsedItem& item,
                Token token,
                T t,
                const Lexer::Coordinate* coo = nullptr)
  {
    item.d_token = token;
    item.d_item  = t;
    if (coo)
    {
      d_work.back().d_coo = *coo;
    }
  }

  template <typename T>
  void push_arg(const T& arg, const Lexer::Coordinate* coo = nullptr)
  {
    ParsedItem& item = item_open();
    item.d_item      = arg;
    item.d_coo       = coo ? *coo : d_lexer->coo();
  }

  uint64_t pop_uint64_arg();
  bitwuzla::Term pop_term_arg();
  std::string pop_str_arg();
  SymbolTable::Node* pop_node_arg(bool set_coo = false);

  uint64_t peek_uint64_arg() const
  {
    assert(peek_is_uint64_arg());
    return std::get<uint64_t>(d_work.back().d_item);
  }
  const bitwuzla::Term& peek_term_arg() const
  {
    assert(peek_is_term_arg());
    return std::get<bitwuzla::Term>(d_work.back().d_item);
  }
  SymbolTable::Node* peek_node_arg() const
  {
    assert(peek_is_node_arg());
    return std::get<SymbolTable::Node*>(d_work.back().d_item);
  }

  uint64_t peek_uint64_arg(size_t idx) const
  {
    assert(peek_is_uint64_arg(idx));
    return std::get<uint64_t>(d_work[idx].d_item);
  }
  const bitwuzla::Term& peek_term_arg(size_t idx) const
  {
    assert(peek_is_term_arg(idx));
    return std::get<bitwuzla::Term>(d_work[idx].d_item);
  }
  const std::string& peek_str_arg(size_t idx) const
  {
    assert(peek_is_str_arg(idx));
    return std::get<std::string>(d_work[idx].d_item);
  }
  SymbolTable::Node* peek_node_arg(size_t idx) const
  {
    assert(peek_is_node_arg(idx));
    return std::get<SymbolTable::Node*>(d_work[idx].d_item);
  }

  bool peek_is_uint64_arg() const
  {
    assert(d_work.back().d_token != Token::IDX
           || std::holds_alternative<uint64_t>(d_work.back().d_item));
    return d_work.back().d_token == Token::IDX;
  }
  bool peek_is_uint64_arg(size_t idx) const
  {
    assert(idx >= d_work.size() || d_work[idx].d_token != Token::IDX
           || std::holds_alternative<uint64_t>(d_work[idx].d_item));
    return idx < d_work.size() && d_work[idx].d_token == Token::IDX;
  }
  bool peek_is_term_arg() const
  {
    assert(d_work.back().d_token != Token::TERM
           || std::holds_alternative<bitwuzla::Term>(d_work.back().d_item));
    return d_work.back().d_token == Token::TERM;
  }
  bool peek_is_term_arg(size_t idx) const
  {
    assert(idx > d_work.size() || d_work[idx].d_token != Token::TERM
           || std::holds_alternative<bitwuzla::Term>(d_work[idx].d_item));
    return idx < d_work.size() && d_work[idx].d_token == Token::TERM;
  }
  bool peek_is_str_arg() const
  {
    assert(d_work.back().d_token != Token::STRING
           || std::holds_alternative<std::string>(d_work.back().d_item));
    return d_work.back().d_token == Token::STRING;
  }
  bool peek_is_str_arg(size_t idx) const
  {
    assert(idx > d_work.size() || d_work[idx].d_token != Token::STRING
           || std::holds_alternative<std::string>(d_work[idx].d_item));
    return idx < d_work.size() && d_work[idx].d_token == Token::STRING;
  }
  bool peek_is_node_arg() const
  {
    assert(d_work.back().d_token != Token::SYMBOL
           || std::holds_alternative<SymbolTable::Node*>(d_work.back().d_item));
    return d_work.back().d_token == Token::SYMBOL;
  }
  bool peek_is_node_arg(size_t idx) const
  {
    assert(idx > d_work.size() || d_work[idx].d_token != Token::SYMBOL
           || std::holds_alternative<SymbolTable::Node*>(d_work[idx].d_item));
    return idx < d_work.size() && d_work[idx].d_token == Token::SYMBOL;
  }

  bool pop_args(const ParsedItem& item_open,
                std::vector<bitwuzla::Term>& args,
                std::vector<uint64_t>* idxs    = nullptr,
                std::vector<std::string>* strs = nullptr);

#ifndef NDEBUG
  void print_work_stack();
  void print_work_control_stack();
#endif

  bitwuzla::Options& d_options;
  std::unique_ptr<bitwuzla::Bitwuzla> d_bitwuzla;
  bitwuzla::Terminator* d_terminator = nullptr;

  const std::string& d_infile_name;

  std::unique_ptr<Lexer> d_lexer;
  SymbolTable d_table;

  /** The log level. */
  uint64_t d_log_level;
  /** The verbosity level. */
  uint64_t d_verbosity;
  /** The associated logger class. */
  util::Logger d_logger;

  std::ofstream d_outfile;
  std::ostream* d_out = &std::cout;

  bool d_print_success = false;
  bool d_global_decl   = false;
  bool d_arrays_enabled = false;
  bool d_bv_enabled     = false;
  bool d_fp_enabled     = false;
  std::string d_logic;

  bitwuzla::Result d_status = bitwuzla::Result::UNKNOWN;
  bitwuzla::Result d_result = bitwuzla::Result::UNKNOWN;
  uint64_t d_scope_level    = 0;

  std::vector<ParsedItem> d_work;
  std::vector<uint64_t> d_work_control;

  uint64_t d_token_class_mask = 0;

  bool d_expect_body    = false;
  bool d_is_sorted_var  = false;
  bool d_is_var_binding = false;
  bool d_done           = false;

  std::string d_error;
  Lexer::Coordinate* d_err_coo = nullptr;

  SymbolTable::Node* d_last_node = nullptr;

  struct Statistics
  {
    Statistics();

    util::Statistics d_stats;

    uint64_t& num_assertions;
    uint64_t& num_check_sat;
    uint64_t& num_commands;
    uint64_t& num_exit;
    uint64_t& num_set_logic;

    util::TimerStatistic& time_parse;

  } d_statistics;
};
}  // namespace parser::smt2
}  // namespace bzla

#endif
