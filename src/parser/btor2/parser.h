/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_BTOR2_PARSER_H_INCLUDED
#define BZLA_PARSER_BTOR2_PARSER_H_INCLUDED

#include "parser/btor2/lexer.h"
#include "parser/parser.h"

namespace bzla {
namespace parser::btor2 {

class Parser : public bzla::parser::Parser
{
 public:
  /**
   * Constructor.
   * @param options     The associated Bitwuzla options. Parser creates
   *                    Bitwuzla instance from these options.
   * @param infile_name The name of the input file.
   * @param out         The output stream.
   */
  Parser(bitwuzla::Options& options,
         const std::string& infile_name,
         std::ostream* out = &std::cout);
  /**
   * Constructor.
   * @param options     The associated Bitwuzla options. Parser creates Bitwuzla
   *                    instance from these options.
   * @param infile_name The name of the input file.
   * @param infile      The input file.
   * @param out         The output stream.
   */
  Parser(bitwuzla::Options& options,
         const std::string& infile_name,
         FILE* infile,
         std::ostream* out = &std::cout);
  /** Destructor. */
  ~Parser();
  /**
   * Parse input file.
   * @param parse_only True to only parse without executing check-sat calls.
   */
  std::string parse(bool parse_only) override;

 private:
  void init();
  bitwuzla::Term bool_term_to_bv1(const bitwuzla::Term& term) const;
  bitwuzla::Term bv1_term_to_bool(const bitwuzla::Term& term) const;

  bool parse_line();
  bool parse_number(bool sign,
                    int64_t& res,
                    bool look_ahead = false,
                    Token la        = Token::INVALID);
  bool parse_sort(int64_t line_id);
  bool parse_term(bitwuzla::Term& res);

  /**
   * Check if the given token is an invalid of eof token and set error message
   * and coordinate on error.
   * @return False on error.
   */
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

  bool error(const std::string& error_msg,
             const std::optional<Lexer::Coordinate>& coo = std::nullopt);
  bool error_invalid();
  bool error_eof();

  std::unordered_map<int64_t, bitwuzla::Sort> d_sort_map;
  std::unordered_map<int64_t, bitwuzla::Term> d_term_map;

  bitwuzla::Term d_bv1_one;
  bitwuzla::Term d_bv1_zero;

  /** The associated BTOR2 lexer. */
  std::unique_ptr<Lexer> d_lexer;

  /** Parse statistics. */
  struct Statistics
  {
    Statistics();

    util::Statistics d_stats;

    /** The overall number of parsed lines. */
    uint64_t& num_lines;

    /**
     * The time required for parsing.
     * @note This is not parse-only, it includes time for any calls to the
     *       solver (check-sat, get-model, ...).
     */
    util::TimerStatistic& time_parse;

  } d_statistics;
};
}  // namespace parser::btor2
}  // namespace bzla

#endif
