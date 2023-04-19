extern "C" {
#include <bitwuzla/c/parser.h>
}
#include <bitwuzla/cpp/parser.h>

#include "api/c/bitwuzla_structs.h"
#include "api/c/checks.h"
#include "api/checks.h"

struct BitwuzlaParser
{
  BitwuzlaParser(BitwuzlaOptions* options,
                 const char* infile_name,
                 FILE* infile,
                 const char* language)
  {
    d_parser.reset(new bitwuzla::parser::Parser(
        options->d_options, infile_name, infile, language));
  }
  /** The associated bitwuzla instance. */
  std::unique_ptr<bitwuzla::parser::Parser> d_parser;
  /** The parser error message. */
  std::string d_error_msg;
  /** The wrapped Bitwuzla instance associated with the parser. */
  std::unique_ptr<Bitwuzla> d_bitwuzla = nullptr;
};

BitwuzlaParser*
bitwuzla_parser_new(BitwuzlaOptions* options,
                    const char* infile_name,
                    FILE* infile,
                    const char* language)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_NOT_NULL(infile_name);
  BITWUZLA_CHECK_NOT_NULL(infile);
  BITWUZLA_CHECK_NOT_NULL(language);
  return new BitwuzlaParser(options, infile_name, infile, language);
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_parser_delete(BitwuzlaParser* parser)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  delete parser;
  BITWUZLA_TRY_CATCH_END;
}

const char*
bitwuzla_parser_parse(BitwuzlaParser* parser, bool parse_only)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  parser->d_error_msg = parser->d_parser->parse(parse_only);
  if (parser->d_error_msg.empty())
  {
    return nullptr;
  }
  return parser->d_error_msg.c_str();
  BITWUZLA_TRY_CATCH_END;
}

Bitwuzla*
bitwuzla_parser_get_bitwuzla(BitwuzlaParser* parser)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  if (!parser->d_bitwuzla)
  {
    parser->d_bitwuzla.reset(new Bitwuzla(parser->d_parser->bitwuzla()));
  }
  return parser->d_bitwuzla.get();
  BITWUZLA_TRY_CATCH_END;
}
