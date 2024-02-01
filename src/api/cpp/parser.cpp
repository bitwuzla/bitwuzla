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

/* -------------------------------------------------------------------------- */

Parser::Parser(Options &options, const std::string &language, std::ostream *out)
{
  BITWUZLA_CHECK(language == "smt2" || language == "btor2")
      << "invalid input language, expected 'smt2' or 'btor2'";
  BITWUZLA_CHECK_NOT_NULL(out);
  if (language == "smt2")
  {
    d_parser.reset(new bzla::parser::smt2::Parser(options, out));
  }
  else
  {
    d_parser.reset(new bzla::parser::btor2::Parser(options, out));
  }
  BITWUZLA_CHECK(d_parser->error_msg().empty()) << d_parser->error_msg();
}

bool
Parser::parse(const std::string &input, bool parse_only, bool parse_file)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(input);
  assert(d_parser);
  return d_parser->parse(input, parse_only, parse_file);
}

bool
Parser::parse(const std::string &infile_name,
              std::istream &input,
              bool parse_only)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(infile_name);
  BITWUZLA_CHECK(input.operator bool()) << "invalid input stream";
  assert(d_parser);
  return d_parser->parse(infile_name, input, parse_only);
}

std::string
Parser::error_msg() const
{
  return d_parser->error_msg();
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
