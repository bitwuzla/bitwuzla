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
  Parser(bitwuzla::Options& options,
         std::istream* infile,
         const std::string& infile_name,
         uint64_t log_level = 0,
         uint64_t verbosity = 0);

  std::string parse();

  void configure_terminator(bitwuzla::Terminator* terminator);

 private:
  struct ParsedItem
  {
    ParsedItem(Token token, const Lexer::Coordinate& coo);
    ParsedItem(Token token,
               const std::string& str,
               const Lexer::Coordinate& coo);
    ParsedItem(Token token,
               SymbolTable::Node* node,
               const Lexer::Coordinate& coo);
    Token d_token;
    std::variant<std::string, SymbolTable::Node*> d_parsed;
    Lexer::Coordinate d_coo;
  };

  bool terminate();

  Token next_token();

  bool parse_command();
  bool parse_command_assert();
  bool parse_command_check_sat();
  bool parse_command_check_sat_assuming();
  bool parse_command_declare_const();
  bool parse_command_declare_sort();
  bool parse_command_declare_fun();
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

  bool parse_symbol(const std::string& error_msg, bool shadow = false);

  bool parse_term(bool look_ahead = false, Token la_char = Token::INVALID);
  bool parse_open_term(Token token);
  bool parse_open_term_as();
  bool parse_open_term_indexed();
  bool parse_open_term_quant();
  bool parse_open_term_symbol();

  bool parse_sort();
  bool parse_sort_array();
  bool parse_sort_bv_fp();

  bool close_term(Token token);
  bool close_term_as();
  bool close_term_bang();
  bool close_term_core();
  bool close_term_array();
  bool close_term_bv();
  bool close_term_fp();
  bool close_term_fun_app();
  bool close_term_let();
  bool close_term_letbind();
  bool close_term_parletbind();
  bool close_term_quant();
  bool close_term_sorted_var();
  bool close_term_sorted_vars();

  void open_term_scope();
  void close_term_scope();

  bool error(const std::string& error_msg,
             const Lexer::Coordinate* coo = nullptr);
  bool error_invalid();
  bool error_eof(Token token);

  bool check_token(Token token);

  bool is_symbol(Token token);

  size_t enable_theory(const std::string& logic,
                       const std::string& theory,
                       size_t size_prefix);
  bool is_supported_logic(const std::string& logic);

  void print_success();

  uint64_t pop_uint64_arg();
  bitwuzla::Sort pop_sort_arg();
  bitwuzla::Term pop_term_arg();
  std::string pop_str_arg();
  SymbolTable::Node* pop_node_arg();

  uint64_t peek_uint64_arg();
  const bitwuzla::Sort& peek_sort_arg();

  std::unique_ptr<Lexer> d_lexer;
  SymbolTable d_table;

  bitwuzla::Options& d_options;
  const std::string& d_infile_name;

  std::unique_ptr<bitwuzla::Bitwuzla> d_bitwuzla;

  bitwuzla::Terminator* d_terminator = nullptr;

  /** The associated logger class. */
  util::Logger d_logger;
  /** The log level. */
  uint64_t d_log_level;
  /** The verbosity level. */
  uint64_t d_verbosity;

  std::ofstream d_outfile;
  std::ostream* d_out = &std::cout;

  bool d_print_success = false;
  bool d_global_decl   = false;
  bool d_arrays_enabled = false;
  bool d_bv_enabled     = false;
  bool d_fp_enabled     = false;
  std::string d_logic;

  bitwuzla::Result d_status;

  std::vector<ParsedItem> d_work;
  std::vector<std::variant<uint64_t,
                           std::string,
                           bitwuzla::Term,
                           bitwuzla::Sort,
                           SymbolTable::Node*>>
      d_work_args;
  std::vector<uint64_t> d_work_args_control;

  uint64_t d_token_class_mask = 0;

  // TODO: this might be redundant with d_work_args_control.size()
  uint64_t d_term_open = 0;

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
