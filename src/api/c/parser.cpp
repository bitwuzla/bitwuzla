/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

extern "C" {
#include <bitwuzla/c/parser.h>
}
#include <bitwuzla/cpp/parser.h>

#include <fstream>
#include <iostream>

#include "api/c/bitwuzla_structs.h"
#include "api/c/checks.h"
#include "api/checks.h"

struct BitwuzlaParser
{
  BitwuzlaParser(BitwuzlaOptions* options,
                 const char* language,
                 uint8_t base,
                 const char* outfile_name)
  {
    std::ofstream outfile;
    std::ostream* out = &std::cout;
    if (std::string(outfile_name) != "<stdout>")
    {
      outfile.open(outfile_name, std::ofstream::out);
      out = &outfile;
    }
    (*out) << bitwuzla::set_bv_format(base);
    d_parser.reset(
        new bitwuzla::parser::Parser(options->d_options, language, out));
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
                    const char* language,
                    uint8_t base,
                    const char* outfile_name)
{
  BitwuzlaParser* res = nullptr;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_NOT_NULL(language);
  BITWUZLA_CHECK_NOT_NULL(outfile_name);
  res = new BitwuzlaParser(options, language, base, outfile_name);
  BITWUZLA_TRY_CATCH_END;
  return res;
}

void
bitwuzla_parser_delete(BitwuzlaParser* parser)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  delete parser;
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_parser_parse(BitwuzlaParser* parser,
                      const char* input,
                      bool parse_only,
                      bool parse_file)
{
  bool res = false;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  BITWUZLA_CHECK_NOT_NULL(input);
  res                 = parser->d_parser->parse(input, parse_only, parse_file);
  parser->d_error_msg = parser->d_parser->error_msg();
  BITWUZLA_TRY_CATCH_END;
  return res;
}

const char*
bitwuzla_parser_get_error_msg(BitwuzlaParser* parser)
{
  const char* res = nullptr;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  res = parser->d_error_msg.c_str();
  BITWUZLA_TRY_CATCH_END;
  return res;
}

Bitwuzla*
bitwuzla_parser_get_bitwuzla(BitwuzlaParser* parser)
{
  Bitwuzla* res = nullptr;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  if (!parser->d_bitwuzla)
  {
    parser->d_bitwuzla.reset(new Bitwuzla(parser->d_parser->bitwuzla().get()));
  }
  res = parser->d_bitwuzla.get();
  BITWUZLA_TRY_CATCH_END;
  return res;
}
