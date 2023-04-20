#include "parser/smt2/parser.h"

#include <bitwuzla/cpp/parser.h>

#include "api/checks.h"
#include "parser/btor2/parser.h"

namespace bitwuzla::parser {

/* -------------------------------------------------------------------------- */

Parser::Parser(Options &options,
               const std::string &infile_name,
               const std::string &language)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(infile_name);
  BITWUZLA_CHECK(language == "smt2" || language == "btor2")
      << "invalid input language, expected 'smt2' or 'btor2'";
  if (language == "smt2")
  {
    d_parser.reset(new bzla::parser::smt2::Parser(options, infile_name));
  }
  else
  {
    d_parser.reset(new bzla::parser::btor2::Parser(options, infile_name));
  }
  BITWUZLA_CHECK(d_parser->error_msg().empty()) << d_parser->error_msg();
}

Parser::Parser(Options &options,
               const std::string &infile_name,
               FILE *infile,
               const std::string &language)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(infile_name);
  BITWUZLA_CHECK(language == "smt2" || language == "btor2")
      << "invalid input language, expected 'smt2' or 'btor2'";
  if (language == "smt2")
  {
    d_parser.reset(
        new bzla::parser::smt2::Parser(options, infile_name, infile));
  }
  else
  {
    d_parser.reset(
        new bzla::parser::btor2::Parser(options, infile_name, infile));
  }
  BITWUZLA_CHECK(d_parser->error_msg().empty()) << d_parser->error_msg();
}

std::string
Parser::parse(bool parse_only)
{
  assert(d_parser);
  return d_parser->parse(parse_only);
}

bitwuzla::Bitwuzla *
Parser::bitwuzla()
{
  return d_parser->bitwuzla();
}

Parser::~Parser() {}

/* -------------------------------------------------------------------------- */

}  // namespace bitwuzla::parser
