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

  bool parse_rpars(uint64_t nrpars);

  SymbolTable::Node* parse_symbol(const std::string& error_msg);

  void error(const std::string& error_msg,
             const Lexer::Coordinate* coo = nullptr);
  void error_invalid();
  void error_eof(Token token);

  bool check_token(Token token);

  size_t enable_theory(const std::string& logic,
                       const std::string& theory,
                       size_t size_prefix);
  bool is_supported_logic(const std::string& logic);
  void print_success();

  std::unique_ptr<Lexer> d_lexer;
  SymbolTable d_table;

  bitwuzla::Options& d_options;
  const std::string& d_infile_name;

  std::unique_ptr<bitwuzla::Bitwuzla> d_bitwuzla;

  bitwuzla::Terminator* d_terminator = nullptr;

  /** The associated logger class. */
  util::Logger d_logger;

  uint64_t d_log_level;
  uint64_t d_verbosity;

  std::ofstream d_outfile;
  std::ostream* d_out = &std::cout;

  bool d_print_success = false;
  bool d_global_decl   = false;
  bool d_done = false;

  std::string d_logic;

  bitwuzla::Result d_status;

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
