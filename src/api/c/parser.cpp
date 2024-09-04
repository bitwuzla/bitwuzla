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
  BitwuzlaParser(BitwuzlaTermManager* tm,
                 BitwuzlaOptions* options,
                 const char* language,
                 uint8_t base,
                 const char* outfile_name)
      : d_tm(tm)
  {
    std::ofstream outfile;
    std::ostream* out = &std::cout;
    if (std::string(outfile_name) != "<stdout>")
    {
      outfile.open(outfile_name, std::ofstream::out);
      out = &outfile;
    }
    (*out) << bitwuzla::set_bv_format(base);
    d_parser.reset(new bitwuzla::parser::Parser(
        tm->d_tm, options->d_options, language, out));
  }
  /** The associated bitwuzla instance. */
  std::unique_ptr<bitwuzla::parser::Parser> d_parser;
  /** The parser error message. */
  std::string d_error_msg;
  /** The wrapped Bitwuzla instance associated with the parser. */
  std::unique_ptr<Bitwuzla> d_bitwuzla = nullptr;
  BitwuzlaTermManager* d_tm            = nullptr;
};

BitwuzlaParser*
bitwuzla_parser_new(BitwuzlaTermManager* tm,
                    BitwuzlaOptions* options,
                    const char* language,
                    uint8_t base,
                    const char* outfile_name)
{
  BitwuzlaParser* res = nullptr;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_NOT_NULL(language);
  BITWUZLA_CHECK_NOT_NULL(outfile_name);
  res = new BitwuzlaParser(tm, options, language, base, outfile_name);
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

void
bitwuzla_parser_configure_auto_print_model(BitwuzlaParser* parser, bool value)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  parser->d_parser->configure_auto_print_model(value);
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_parser_parse(BitwuzlaParser* parser,
                      const char* input,
                      bool parse_only,
                      bool parse_file,
                      const char** error_msg)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  BITWUZLA_CHECK_NOT_NULL(input);
  BITWUZLA_CHECK_NOT_NULL(error_msg);
  try
  {
    parser->d_parser->parse(input, parse_only, parse_file);
    *error_msg = nullptr;
  }
  catch (bitwuzla::Exception& e)
  {
    parser->d_error_msg = e.what();
    *error_msg =
        parser->d_error_msg.empty() ? NULL : parser->d_error_msg.c_str();
  }
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_parser_parse_term(BitwuzlaParser* parser,
                           const char* input,
                           const char** error_msg)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  BITWUZLA_CHECK_NOT_NULL(input);
  BITWUZLA_CHECK_NOT_NULL(error_msg);
  try
  {
    res        = parser->d_tm->export_term(parser->d_parser->parse_term(input));
    *error_msg = nullptr;
  }
  catch (bitwuzla::Exception& e)
  {
    parser->d_error_msg = e.what();
    *error_msg =
        parser->d_error_msg.empty() ? NULL : parser->d_error_msg.c_str();
  }
  BITWUZLA_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_parser_parse_sort(BitwuzlaParser* parser,
                           const char* input,
                           const char** error_msg)
{
  BitwuzlaSort res = 0;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  BITWUZLA_CHECK_NOT_NULL(input);
  BITWUZLA_CHECK_NOT_NULL(error_msg);
  try
  {
    res        = parser->d_tm->export_sort(parser->d_parser->parse_sort(input));
    *error_msg = nullptr;
  }
  catch (bitwuzla::parser::Exception& e)
  {
    parser->d_error_msg = e.what();
    *error_msg =
        parser->d_error_msg.empty() ? NULL : parser->d_error_msg.c_str();
  }
  BITWUZLA_TRY_CATCH_END;
  return res;
}

BitwuzlaSort*
bitwuzla_parser_get_declared_sorts(BitwuzlaParser* parser, size_t* size)
{
  BitwuzlaSort* res = nullptr;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  auto decl_sorts = parser->d_parser->get_declared_sorts();
  static thread_local std::vector<BitwuzlaSort> c_sorts;
  c_sorts.clear();
  for (const auto& s : decl_sorts)
  {
    c_sorts.push_back(parser->d_tm->export_sort(s));
  }
  *size = c_sorts.size();
  res   = *size ? c_sorts.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm*
bitwuzla_parser_get_declared_funs(BitwuzlaParser* parser, size_t* size)
{
  BitwuzlaTerm* res = nullptr;
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(parser);
  auto decl_funs = parser->d_parser->get_declared_funs();
  static thread_local std::vector<BitwuzlaTerm> c_terms;
  c_terms.clear();
  for (const auto& f : decl_funs)
  {
    c_terms.push_back(parser->d_tm->export_term(f));
  }
  *size = c_terms.size();
  res   = *size ? c_terms.data() : nullptr;
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
    parser->d_bitwuzla.reset(
        new Bitwuzla(parser->d_tm, parser->d_parser->bitwuzla().get()));
  }
  res = parser->d_bitwuzla.get();
  BITWUZLA_TRY_CATCH_END;
  return res;
}
