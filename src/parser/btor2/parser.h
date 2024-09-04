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
   * @param options  The associated Bitwuzla options. Parser creates Bitwuzla
   *                 instance from these options.
   * @param out      The output stream.
   */
  Parser(bitwuzla::TermManager& tm,
         bitwuzla::Options& options,
         std::ostream* out = &std::cout);
  /** Destructor. */
  ~Parser();

  bool parse(const std::string& input,
             bool parse_only,
             bool parse_file) override;
  bool parse(const std::string& infile_name,
             std::istream& input,
             bool parse_only) override;

  bool parse_term(const std::string& input, bitwuzla::Term& res) override;
  bool parse_sort(const std::string& input, bitwuzla::Sort& res) override;
  std::vector<bitwuzla::Sort> get_declared_sorts() const override;
  std::vector<bitwuzla::Term> get_declared_funs() const override;

 private:
  enum class ParsedKind
  {
    CONSTRAINT,
    SORT,
    TERM,
  };

  bool print_model();

  /** Reset parser for new parse call. */
  void reset();

  /** Helper to convert boolean term to bit-vector term of size 1. */
  bitwuzla::Term bool_term_to_bv1(const bitwuzla::Term& term) const;
  /** Helper to convert bit-vector term of size 1 to boolean term. */
  bitwuzla::Term bv1_term_to_bool(const bitwuzla::Term& term) const;

  /**
   * Parse a line.
   * @param pkind Optional output parameter indicating what kind of line
   *              was parsed. This is mainly used in the public parsing
   *              functions parse_term() and parse_sort().
   * @param id    Optional output parameter for the resulting parsed
   *              line id. This is mainly used in the public parsing
   *              functions parse_term() and parse_sort().
   * @return False on error.
   */
  bool parse_line(ParsedKind* pkind = nullptr, int64_t* line_id = nullptr);
  /**
   * Parse a numeral.
   * @param sign       True if parsed numeral may be signed.
   * @param res        Output parameter to store the resulting term id.
   * @param look_ahead True if we have a look ahead token.
   * @param la         The look ahead token.
   * @return False on error.
   */
  bool parse_number(bool sign,
                    int64_t& res,
                    bool look_ahead = false,
                    Token la        = Token::INVALID);

  const char* parse_opt_symbol();

  /**
   * Parse sort.
   * @param line_id The line id of the sort to parse.
   * @return False on error.
   */
  bool parse_sort(int64_t line_id);
  /**
   * Parse term.
   * @param res Output parameter to store the resulting term.
   * @return False on error.
   */
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

  /**
   * Set error message and error coordinate.
   * @param error_msg The error message.
   * @param coo       The error coordinate. Set to the current coordinate of
   *                  the lexer if not given.
   * @return Always returns false to allow using the result of this function
   *         call to indicate a parse error.
   */
  bool error(const std::string& error_msg,
             const std::optional<Lexer::Coordinate>& coo = std::nullopt);
  /**
   * Set error message and coordinate for errors where the current token is
   * invalid.
   * @return Always returns false to allow using the result of this function
   *         call to indicate a parse error.
   */
  bool error_invalid();
  /**
   * Set error message and coordinate for errors where the current token is
   * the end-of-file token.
   * @return Always returns false to allow using the result of this function
   *         call to indicate a parse error.
   */
  bool error_eof();

  /** Map line id to sort. */
  std::unordered_map<int64_t, bitwuzla::Sort> d_sort_map;
  /** Map line id to term. */
  std::unordered_map<int64_t, bitwuzla::Term> d_term_map;
  std::vector<std::pair<int64_t, bitwuzla::Term>> d_inputs;

  /** Term representing bit-vector one of size 1 (true). */
  bitwuzla::Term d_bv1_one;
  /** Term representing bit-vector one of size 1 (false). */
  bitwuzla::Term d_bv1_zero;

  /** The associated BTOR2 lexer. */
  std::unique_ptr<Lexer> d_lexer;

  bool d_parse_only = false;

  std::vector<std::tuple<bitwuzla::Term, int64_t, std::string>>
      d_bad_properties;

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
