#ifndef BZLA_PARSER_SMT2_PARSER_H_INCLUDED
#define BZLA_PARSER_SMT2_PARSER_H_INCLUDED

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
  Parser(std::istream* infile,
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

  void error(const std::string& error_msg,
             const Lexer::Coordinate* coo = nullptr);

  std::unique_ptr<Lexer> d_lexer;
  SymbolTable d_table;

  const std::string& d_infile_name;

  std::unique_ptr<bitwuzla::Bitwuzla> d_bitwuzla;

  bitwuzla::Terminator* d_terminator = nullptr;

  /** The associated logger class. */
  util::Logger d_logger;

  uint64_t d_log_level;
  uint64_t d_verbosity;
  bool d_done = false;

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
