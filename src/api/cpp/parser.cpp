/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/btor2/parser.h"

#include <bitwuzla/cpp/parser.h>

#include "api/checks.h"
#include "parser/smt2/parser.h"

namespace bitwuzla::parser {

/* Exception public --------------------------------------------------------- */

Exception::Exception(const std::string &msg) : bitwuzla::Exception(msg) {}

Exception::Exception(const std::stringstream &stream)
    : bitwuzla::Exception(stream.str())
{
}

/* Parser public ------------------------------------------------------------ */

Parser::Parser(TermManager &tm,
               Options &options,
               const std::string &language,
               std::ostream *out)
{
  BITWUZLA_CHECK(language == "smt2" || language == "btor2")
      << "invalid input language, expected 'smt2' or 'btor2'";
  BITWUZLA_CHECK_NOT_NULL(out);
  if (language == "smt2")
  {
    d_parser.reset(new bzla::parser::smt2::Parser(tm, options, out));
  }
  else
  {
    d_parser.reset(new bzla::parser::btor2::Parser(tm, options, out));
  }
  BITWUZLA_CHECK(d_parser->error_msg().empty()) << d_parser->error_msg();
}

void
Parser::parse(const std::string &input, bool parse_only, bool parse_file)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(input);
  assert(d_parser);
  if (!d_parser->parse(input, parse_only, parse_file))
  {
    throw Exception(d_parser->error_msg());
  }
}

void
Parser::configure_auto_print_model(bool value)
{
  assert(d_parser);
  d_parser->configure_auto_print_model(value);
}

void
Parser::parse(const std::string &infile_name,
              std::istream &input,
              bool parse_only)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(infile_name);
  BITWUZLA_CHECK(input.operator bool()) << "invalid input stream";
  assert(d_parser);
  if (!d_parser->parse(infile_name, input, parse_only))
  {
    throw Exception(d_parser->error_msg());
  }
}

bitwuzla::Term
Parser::parse_term(const std::string &input)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(input);
  assert(d_parser);
  bitwuzla::Term res;
  if (!d_parser->parse_term(input, res))
  {
    throw Exception(d_parser->error_msg());
  }
  return res;
}

bitwuzla::Sort
Parser::parse_sort(const std::string &input)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(input);
  assert(d_parser);
  bitwuzla::Sort res;
  if (!d_parser->parse_sort(input, res))
  {
    throw Exception(d_parser->error_msg());
  }
  return res;
}

std::vector<Sort>
Parser::get_declared_sorts() const
{
  assert(d_parser);
  return d_parser->get_declared_sorts();
}

std::vector<Term>
Parser::get_declared_funs() const
{
  assert(d_parser);
  return d_parser->get_declared_funs();
}

std::shared_ptr<bitwuzla::Bitwuzla>
Parser::bitwuzla()
{
  BITWUZLA_CHECK(d_parser->bitwuzla() != nullptr)
      << "Bitwuzla instance not yet initialized";
  return d_parser->bitwuzla();
}

Parser::~Parser() {}

/* -------------------------------------------------------------------------- */

}  // namespace bitwuzla::parser
