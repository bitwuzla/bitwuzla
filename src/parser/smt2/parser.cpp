#include "parser/smt2/parser.h"

#include <algorithm>
#include <iostream>

#include "bitwuzla/cpp/bitwuzla.h"

namespace bzla {
namespace parser::smt2 {

/* Parser public ------------------------------------------------------------ */

Parser::Parser(bitwuzla::Options& options,
               std::istream* infile,
               const std::string& infile_name,
               uint64_t log_level,
               uint64_t verbosity)
    : d_options(options),
      d_lexer(new Lexer(infile)),
      d_infile_name(infile_name),
      d_logger(log_level, verbosity),
      d_log_level(log_level),
      d_verbosity(verbosity)
{
  d_token_class_mask = static_cast<uint32_t>(TokenClass::COMMAND)
                       | static_cast<uint32_t>(TokenClass::CORE)
                       | static_cast<uint32_t>(TokenClass::KEYWORD)
                       | static_cast<uint32_t>(TokenClass::RESERVED);
}

std::string
Parser::parse()
{
  util::Timer timer(d_statistics.time_parse);

  while (parse_command() && !d_done && !terminate())
    ;

  // this should be in parser, and parser has to store the msg of lexer
  if (d_lexer->error()) return d_lexer->error_msg();

  if (!terminate() && d_verbosity)
  {
    if (d_statistics.num_commands == 0)
    {
      Msg(1) << "warning: no commands in '" << d_infile_name << "'";
    }
    else
    {
      if (d_statistics.num_set_logic == 0)
      {
        Msg(1) << "warning: no 'set-logic' command in '" << d_infile_name
               << "'";
      }
      if (d_statistics.num_assertions == 0)
      {
        Msg(1) << "warning: no 'assert' command in '" << d_infile_name << "'";
      }
      if (d_statistics.num_check_sat == 0)
      {
        Msg(1) << "warning: no 'check-sat' command in '" << d_infile_name
               << "'";
      }
      if (d_statistics.num_exit == 0)
      {
        Msg(1) << "warning: no 'exit' command in '" << d_infile_name << "'";
      }
    }
  }

  Msg(1) << "parsed " << d_statistics.num_commands << " in "
         << d_statistics.time_parse.elapsed() << " seconds";
}

void
Parser::configure_terminator(bitwuzla::Terminator* terminator)
{
  if (d_bitwuzla)
  {
    d_bitwuzla->configure_terminator(terminator);
  }
  d_terminator = terminator;
}

/* Parser private ----------------------------------------------------------- */

bool
Parser::terminate()
{
  return d_terminator != nullptr && d_terminator->terminate();
}

Token
Parser::next_token()
{
  assert(d_lexer);
  Token token = d_lexer->next_token();
  if (token == Token::SYMBOL || token == Token::ATTRIBUTE)
  {
    assert(d_lexer->has_token());
    SymbolTable::Node* node = d_table.find(d_lexer->token());
    if (!node)
    {
      node = d_table.insert(token, d_lexer->token());
    }
    d_last_node = node;
  }
  return token;
}

bool
Parser::parse_command()
{
  Token token = next_token();

  if (!check_token(token))
  {
    return false;
  }

  if (token != Token::LPAR)
  {
    assert(d_lexer->has_token());
    return error("expected '(' at '" + d_lexer->token() + "'");
  }

  token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (!is_token_class(token, TokenClass::COMMAND))
  {
    assert(d_lexer->has_token());
    return error("expected command at '" + d_lexer->token() + "'");
  }

  switch (token)
  {
    case Token::ASSERT: return parse_command_assert();
    case Token::CHECK_SAT: return parse_command_check_sat();
    case Token::CHECK_SAT_ASSUMING: return parse_command_check_sat_assuming();
    case Token::DECLARE_CONST: return parse_command_declare_const();
    case Token::DECLARE_SORT: return parse_command_declare_sort();
    case Token::DECLARE_FUN: return parse_command_declare_fun();
    case Token::DEFINE_FUN: return parse_command_define_fun();
    case Token::DEFINE_SORT: return parse_command_define_sort();
    case Token::ECHO: return parse_command_echo();
    case Token::EXIT: return parse_command_exit();
    case Token::GET_MODEL: return parse_command_get_model();
    case Token::GET_UNSAT_ASSUMPTIONS:
      return parse_command_get_unsat_assumptions();
    case Token::GET_UNSAT_CORE: return parse_command_get_unsat_core();
    case Token::GET_VALUE: return parse_command_get_value();
    case Token::POP: return parse_command_pop();
    case Token::PUSH: return parse_command_push();
    case Token::SET_INFO: return parse_command_set_info();
    case Token::SET_LOGIC: return parse_command_set_logic();
    case Token::SET_OPTION: return parse_command_set_option();

    default:
      assert(d_lexer->has_token());
      return error("unsupported command '" + d_lexer->token() + "'");
  }

  d_statistics.num_commands += 1;
  return true;
}

bool
Parser::parse_command_assert()
{
  //    case BZLA_ASSERT_TAG_SMT2:
  //      if (!parse_term_smt2(parser, &exp, &coo)) return 0;
  //      assert(!parser->error);
  //      if (!bitwuzla_term_is_bool(exp))
  //      {
  //        parser->perrcoo = coo;
  //        return !perr_smt2(parser, "assert argument is not a formula");
  //      }
  //      if (!read_rpar_smt2(parser, " after asserted expression"))
  //      {
  //        return 0;
  //      }
  //      bitwuzla_assert(get_bitwuzla(parser), exp);
  //      assert(!parser->error);
  //      parser->commands.asserts++;
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_check_sat()
{
  //    case BZLA_CHECK_SAT_TAG_SMT2:
  //      configure_smt_comp_mode(parser);
  //      if (!read_rpar_smt2(parser, " after 'check-sat'")) return 0;
  //      if (!check_sat(parser, 0, NULL)) return 0;
  //      break;
}

bool
Parser::parse_command_check_sat_assuming()
{
  //    case BZLA_CHECK_SAT_ASSUMING_TAG_SMT2:
  //      configure_smt_comp_mode(parser);
  //      if (!read_lpar_smt2(parser, " after 'check-sat-assuming'")) return 0;
  //      if (false
  //          && !bitwuzla_get_option(parser->options,
  //          BITWUZLA_OPT_INCREMENTAL))
  //        return !perr_smt2(parser, "incremental solving is not enabled");
  //      if (!read_exp_list(parser, &exps, &coo))
  //      {
  //        BZLA_RELEASE_STACK(exps);
  //        return 0;
  //      }
  //      for (i = 0; i < BZLA_COUNT_STACK(exps); i++)
  //      {
  //        exp = BZLA_PEEK_STACK(exps, i);
  //        if (bitwuzla_term_is_array(exp))
  //        {
  //          parser->perrcoo = coo;
  //          BZLA_RELEASE_STACK(exps);
  //          return !perr_smt2(
  //              parser, "assumption argument is an array and not a formula");
  //        }
  //      }
  //      if (!read_rpar_smt2(parser, " after 'check-sat-assuming'"))
  //      {
  //        BZLA_RELEASE_STACK(exps);
  //        return 0;
  //      }
  //      if (!check_sat(parser, BZLA_COUNT_STACK(exps), exps.start)) return 0;
  //      for (i = 0; i < BZLA_COUNT_STACK(exps); i++)
  //      {
  //        exp = BZLA_PEEK_STACK(exps, i);
  //        BZLA_PUSH_STACK(parser->sat_assuming_assumptions, exp);
  //      }
  //      BZLA_RELEASE_STACK(exps);
  //      BZLA_RESET_STACK(parser->tokens);
  //      break;
}

bool
Parser::parse_command_declare_const()
{
  //    case BZLA_DECLARE_CONST_TAG_SMT2:
  //      if (!declare_fun_smt2(parser, true)) return 0;
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_declare_fun()
{
  //    case BZLA_DECLARE_FUN_TAG_SMT2:
  //      if (!declare_fun_smt2(parser, false)) return 0;
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_declare_sort()
{
  //    case BZLA_DECLARE_SORT_TAG_SMT2:
  //      configure_smt_comp_mode(parser);
  //      if (!declare_sort_smt2(parser)) return 0;
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_define_fun()
{
  //    case BZLA_DEFINE_FUN_TAG_SMT2:
  //      if (!define_fun_smt2(parser)) return 0;
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_define_sort()
{
  //    case BZLA_DEFINE_SORT_TAG_SMT2:
  //      if (!define_sort_smt2(parser)) return 0;
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_echo()
{
  //    case BZLA_ECHO_TAG_SMT2:
  //      if (!echo_smt2(parser)) return 0;
  //      break;
}

bool
Parser::parse_command_exit()
{
  //    case BZLA_EXIT_TAG_SMT2:
  //      if (!read_rpar_smt2(parser, " after 'exit'")) return 0;
  //      assert(!parser->commands.exits);
  //      parser->commands.exits++;
  //      parser->done = true;
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_get_model()
{
  //    case BZLA_GET_MODEL_TAG_SMT2:
  //      if (!read_rpar_smt2(parser, " after 'get-model'")) return 0;
  //      if (!bitwuzla_get_option(parser->options,
  //      BITWUZLA_OPT_PRODUCE_MODELS))
  //        return !perr_smt2(parser, "model generation is not enabled");
  //      if (parser->res->result != BITWUZLA_SAT) break;
  //      // if (bitwuzla_get_option(parser->options,
  //      BITWUZLA_OPT_OUTPUT_FORMAT)
  //      //     == BZLA_OUTPUT_FORMAT_BTOR)
  //      //{
  //      //   // bitwuzla_print_model(bitwuzla, "btor", parser->outfile);
  //      // }
  //      // else
  //      //{
  //      //   // bitwuzla_print_model(bitwuzla, "smt2", parser->outfile);
  //      // }
  //      fflush(parser->outfile);
  //      break;
}

bool
Parser::parse_command_get_unsat_assumptions()
{
  //    case BZLA_GET_UNSAT_ASSUMPTIONS_TAG_SMT2: {
  //      if (!read_rpar_smt2(parser, " after 'get-unsat-assumptions'")) return
  //      0; if (parser->res->result != BITWUZLA_UNSAT) break; fputc('(',
  //      parser->outfile); size_t size; failed_assumptions =
  //          bitwuzla_get_unsat_assumptions(get_bitwuzla(parser), &size);
  //      for (i = 0; i < size; ++i)
  //      {
  //        if (i > 0) fputc(' ', parser->outfile);
  //        const char *symbol =
  //        bitwuzla_term_get_symbol(failed_assumptions[i]); if (symbol)
  //        {
  //          fprintf(parser->outfile, "%s", symbol);
  //        }
  //        else
  //        {
  //          bitwuzla_term_dump(failed_assumptions[i], "smt2",
  //          parser->outfile);
  //        }
  //      }
  //      failed_assumptions = 0;
  //      fputs(")\n", parser->outfile);
  //      fflush(parser->outfile);
  //      break;
  //    }
}

bool
Parser::parse_command_get_unsat_core()
{
  //    case BZLA_GET_UNSAT_CORE_TAG_SMT2: {
  //      if (!read_rpar_smt2(parser, " after 'get-unsat-assumptions'")) return
  //      0; if (parser->res->result != BITWUZLA_UNSAT) break; fputc('(',
  //      parser->outfile); size_t size; unsat_core =
  //      bitwuzla_get_unsat_core(get_bitwuzla(parser), &size); const char *sym;
  //      bool printed_first = false;
  //      for (i = 0; i < size; ++i)
  //      {
  //        sym = bitwuzla_term_get_symbol(unsat_core[i]);
  //        if (!sym) continue;
  //        if (printed_first)
  //        {
  //          fputc(' ', parser->outfile);
  //        }
  //        fprintf(parser->outfile, "%s", sym);
  //        printed_first = true;
  //      }
  //      unsat_core = 0;
  //      fputs(")\n", parser->outfile);
  //      fflush(parser->outfile);
  //      break;
  //    }
}

bool
Parser::parse_command_get_value()
{
  //    case BZLA_GET_VALUE_TAG_SMT2: {
  //      if (!read_lpar_smt2(parser, " after 'get-value'")) return 0;
  //      if (!bitwuzla_get_option(parser->options,
  //      BITWUZLA_OPT_PRODUCE_MODELS))
  //      {
  //        return !perr_smt2(parser, "model generation is not enabled");
  //      }
  //      if (parser->res->result != BITWUZLA_SAT) break;
  //      if (!read_exp_list(parser, &exps, &coo))
  //      {
  //        BZLA_RELEASE_STACK(exps);
  //        return 0;
  //      }
  //      if (!read_rpar_smt2(parser, " after 'get-value'"))
  //      {
  //        BZLA_RELEASE_STACK(exps);
  //        return 0;
  //      }
  //      fputc('(', parser->outfile);
  //      char *symbols = parser->tokens.start;
  //      for (i = 0; i < BZLA_COUNT_STACK(exps); i++)
  //      {
  //        if (BZLA_COUNT_STACK(exps) > 1) fputs("\n ", parser->outfile);
  //        exp = BZLA_PEEK_STACK(exps, i);
  //        bitwuzla_term_print_value_smt2(
  //            parser->bitwuzla, exp, symbols, parser->outfile);
  //        symbols += strlen(symbols) + 1;
  //        assert(symbols <= parser->tokens.top);
  //      }
  //      if (BZLA_COUNT_STACK(exps) > 1) fputc('\n', parser->outfile);
  //      fprintf(parser->outfile, ")\n");
  //      fflush(parser->outfile);
  //      BZLA_RELEASE_STACK(exps);
  //      BZLA_RESET_STACK(parser->tokens);
  //      break;
  //    }
}

bool
Parser::parse_command_pop()
{
  //    case BZLA_POP_TAG_SMT2:
  //      (void) parse_uint64_smt2(parser, true, &level);
  //      if (!read_rpar_smt2(parser, " after 'pop'")) return 0;
  //      if (level > parser->scope_level)
  //      {
  //        return !perr_smt2(parser,
  //                          "popping more scopes (%u) than created via push
  //                          (%u)", level, parser->scope_level);
  //      }
  //      for (i = 0; i < level; i++) close_current_scope(parser);
  //      bitwuzla_pop(get_bitwuzla(parser), level);
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_push()
{
  //    case BZLA_PUSH_TAG_SMT2:
  //      level = 0;
  //      (void) parse_uint64_smt2(parser, true, &level);
  //      if (!read_rpar_smt2(parser, " after 'push'")) return 0;
  //      for (i = 0; i < level; i++) open_new_scope(parser);
  //      configure_smt_comp_mode(parser);
  //      bitwuzla_push(get_bitwuzla(parser), level);
  //      print_success(parser);
  //      break;
}

bool
Parser::parse_command_set_info()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (token != Token::ATTRIBUTE)
  {
    return error("missing keyword after 'set-info'");
  }
  if (token == Token::STATUS)
  {
    token = next_token();
    if (!check_token(token))
    {
      return false;
    }
    if (token != Token::SYMBOL)
    {
      return error("invalid value for ':status'");
    }
    assert(d_lexer->has_token());
    const std::string& status = d_lexer->token();
    if (status == "sat")
    {
      d_status = bitwuzla::Result::SAT;
    }
    else if (status == "unsat")
    {
      d_status = bitwuzla::Result::UNSAT;
    }
    else if (status == "unknown")
    {
      d_status = bitwuzla::Result::UNKNOWN;
    }
    else
    {
      return error("invalid value '" + status + "' for ':status'");
    }
    Msg(1) << "parsed status '" << d_status << "'";
  }
  if (parse_rpars(1))
  {
    print_success();
    return true;
  }
  return false;
}

bool
Parser::parse_command_set_logic()
{
  if (!parse_symbol(" after 'set-logic'"))
  {
    return false;
  }
  SymbolTable::Node* logic = pop_node_arg();
  assert(logic->has_symbol());
  d_logic = logic->d_symbol;
  if (!is_supported_logic(d_logic))
  {
    return error("unsupported logic '" + d_logic + "'");
  }
  Msg(1) << "logic " << d_logic;
  if (parse_rpars(1))
  {
    if (d_statistics.num_set_logic++)
    {
      Msg(1) << "warning: additional 'set-logic' command";
    }
    print_success();
    return true;
  }
  return false;
}

bool
Parser::parse_command_set_option()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (token == Token::RPAR)
  {
    return error("missing keyword after 'set-option'");
  }

  if (token == Token::REGULAR_OUTPUT_CHANNEL)
  {
    token = next_token();
    if (!check_token(token))
    {
      return false;
    }
    const std::string& outfile_name = d_lexer->token();
    assert(!outfile_name.empty());
    try
    {
      d_outfile.open(outfile_name, std::ofstream::out);
    }
    catch (...)
    {
      return error("cannot create '" + outfile_name + "'");
    }
    d_out = &d_outfile;
  }
  else if (token == Token::PRINT_SUCCESS)
  {
    token = next_token();
    if (!check_token(token))
    {
      return false;
    }
    if (token == Token::TRUE)
    {
      d_print_success = true;
      // configure_smt_comp_mode();
    }
    else if (token == Token::FALSE)
    {
      d_print_success = false;
    }
    else
    {
      assert(d_lexer->has_token());
      return error("expected Boolean argument at '" + d_lexer->token() + "'");
    }
  }
  else if (token == Token::GLOBAL_DECLARATIONS)
  {
    token = next_token();
    if (!check_token(token))
    {
      return false;
    }
    if (token == Token::TRUE)
    {
      d_global_decl = true;
    }
    else if (token == Token::FALSE)
    {
      d_global_decl = false;
    }
    else
    {
      assert(d_lexer->has_token());
      return error("expected Boolean argument at '" + d_lexer->token() + "'");
    }
  }
  else if (token == Token::PRODUCE_UNSAT_ASSUMPTIONS)
  {
    // nothing to do, always true
  }
  // Bitwuzla options
  else
  {
    assert(d_lexer->has_token());
    std::string opt = d_lexer->token();
    token           = next_token();
    if (!check_token(token))
    {
      return false;
    }
    assert(d_lexer->has_token());
    try
    {
      d_options.set(opt, d_lexer->token());
    }
    catch (bitwuzla::Exception& e)
    {
      return error(e.msg());
    }
  }
  if (parse_rpars(1))
  {
    print_success();
    return true;
  }
  return false;
}

/* -------------------------------------------------------------------------- */

bool
Parser::parse_lpars(uint64_t nlpars)
{
  while (nlpars > 0)
  {
    Token token = next_token();
    if (token != Token::LPAR)
    {
      return error("missing '('");
    }
    nlpars -= 1;
  }
  return true;
}

bool
Parser::parse_rpars(uint64_t nrpars)
{
  while (nrpars > 0)
  {
    Token token = next_token();
    if (token == Token::ENDOFFILE)
    {
      if (nrpars > 0)
      {
        return error("missing ')' at end of file");
      }
      return true;
    }
    if (token != Token::RPAR)
    {
      return error("missing ')'");
    }
    nrpars -= 1;
  }
  return true;
}

bool
Parser::parse_uint64()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (token == Token::DECIMAL_VALUE)
  {
    assert(d_lexer->has_token());
    try
    {
      uint64_t val = std::stoll(d_lexer->token());
      d_work_args.push_back(val);
      return true;
    }
    catch (...)
    {
      return error("invalid 64 bit integer '" + d_lexer->token() + "'");
    }
  }
  return error("expected decimal value");
}

bool
Parser::parse_symbol(const std::string& error_msg, bool shadow)
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (token != Token::SYMBOL)
  {
    return error("expected symbol" + error_msg);
  }
  assert(d_last_node->d_token == Token::SYMBOL);
  // shadow previously defined symbols
  if (shadow && d_last_node->d_coo.line)
  {
    d_last_node        = d_table.insert(token, d_lexer->token());
    d_last_node->d_coo = d_lexer->coo();
  }
  d_work_args.push_back(d_last_node);
  return true;
}

/* -------------------------------------------------------------------------- */

bool
Parser::parse_term(bool look_ahead, Token la_char)
{
  /* Note: we need look ahead and tokens string only for get-value
   *       (for parsing a term list and printing the originally parsed,
   *       non-simplified expression) */
  Token token;
  bitwuzla::Term res;
  d_term_open = 0;

  do
  {
    if (look_ahead)
    {
      token      = la_char;
      look_ahead = false;
    }
    else
    {
      token = next_token();
    }
    if (!check_token(token))
    {
      return false;
    }

    if (token == Token::RPAR)
    {
      if (!close_term(token))
      {
        return false;
      }
    }
    else
    {
      if (!parse_open_term(token))
      {
        return false;
      }
    }
  } while (d_term_open > 0);
  assert(d_work_args.size() > 0);
  return true;
}

bool
Parser::parse_open_term(Token token)
{
  d_expect_body = false;

  if (token == Token::LPAR)
  {
    open_term_scope();
    if (d_is_var_binding)
    {
      d_work.emplace_back(Token::LETBIND, d_lexer->coo());
      d_is_var_binding          = false;
      if (!parse_symbol("", true))
      {
        return false;
      }
    }
    else if (d_is_sorted_var)
    {
      // parse <sorted_var>: <symbol> <sort>
      d_work.emplace_back(Token::SORTED_VAR, d_lexer->coo());
      d_is_sorted_var           = false;
      if (!parse_symbol(" in sorted var", true))
      {
        return false;
      }
      if (!parse_sort())
      {
        return false;
      }
      bitwuzla::Sort sort = pop_sort_arg();
      SymbolTable::Node* symbol = pop_node_arg();
      assert(symbol->has_symbol());
      d_work_args.push_back(bitwuzla::mk_var(sort, symbol->d_symbol));
    }
  }
  else if (d_is_var_binding)
  {
    return error("expected var binding");
  }
  else if (d_is_sorted_var)
  {
    return error("expected sorted variable");
  }
  else if (is_symbol(token))
  {
    d_work.emplace_back(token, d_last_node, d_lexer->coo());
    if (!parse_open_term_symbol())
    {
      return false;
    }
  }
  else if (token == Token::NAMED)
  {
    d_work_args.push_back(d_last_node);
    if (!parse_symbol(" in sorted var", true))
    {
      return false;
    }
    SymbolTable::Node* symbol = peek_node_arg();
    assert(symbol->has_symbol());
    if (symbol->d_coo.line)
    {
      return error("symbol '" + symbol->d_symbol + "' already defined at line "
                   + std::to_string(symbol->d_coo.line) + " column "
                   + std::to_string(symbol->d_coo.col));
    }
    symbol->d_coo = d_lexer->coo();
  }
  else if (token == Token::BINARY_VALUE)
  {
    assert(d_lexer->has_token());
    std::string val     = d_lexer->token().substr(2);
    bitwuzla::Sort sort = bitwuzla::mk_bv_sort(val.size());
    d_work_args.push_back(bitwuzla::mk_bv_value(sort, val));
  }
  else if (token == Token::HEXADECIMAL_VALUE)
  {
    assert(d_lexer->has_token());
    std::string val     = d_lexer->token().substr(2);
    bitwuzla::Sort sort = bitwuzla::mk_bv_sort(val.size() * 4);
    d_work_args.push_back(bitwuzla::mk_bv_value(sort, val, 16));
  }
  else if (token == Token::DECIMAL_VALUE || token == Token::REAL_VALUE)
  {
    assert(d_lexer->has_token());
    d_work_args.push_back(d_lexer->token().empty());
  }
  else
  {
    return error("unexpected token");
  }
  return true;
}

bool
Parser::parse_open_term_as()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }

  if (token != Token::SYMBOL)
  {
    return error("expected identifier");
  }

  SymbolTable::Node* node = d_last_node;
  assert(node);
  assert(node->has_symbol());
  const std::string& iden = node->d_symbol;

  if (iden == "const" || iden == "const-array")
  {
    if (!parse_sort())
    {
      return false;
    }
    const bitwuzla::Sort& sort = peek_sort_arg();
    if (!sort.is_array())
    {
      return error("expected array sort");
    }
    if (!parse_rpars(1))
    {
      return false;
    }
    assert(nargs() == 1);
    // ((as const(-array) <sort>) <term>) -> (as const(-array) sort term)
    close_term_scope();
    return true;
  }
  return error("invalid identifier '" + iden + "'");
}

bool
Parser::parse_open_term_indexed()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }

  Lexer::Coordinate coo   = d_lexer->coo();
  Token token_kind        = token;
  bitwuzla::Kind kind     = bitwuzla::Kind::VALUE;
  SymbolTable::Node* node = d_last_node;

  bool allow_zero = false;
  uint64_t nidxs  = 1;

  switch (token)
  {
    case Token::BV_REPEAT:
      kind       = bitwuzla::Kind::BV_REPEAT;
      allow_zero = true;
      break;

    case Token::BV_ROTATE_LEFT:
      kind       = bitwuzla::Kind::BV_ROLI;
      allow_zero = true;
      break;

    case Token::BV_ROTATE_RIGHT:
      kind       = bitwuzla::Kind::BV_RORI;
      allow_zero = true;
      break;

    case Token::BV_SIGN_EXTEND:
      kind       = bitwuzla::Kind::BV_SIGN_EXTEND;
      allow_zero = true;
      break;

    case Token::BV_ZERO_EXTEND:
      kind       = bitwuzla::Kind::BV_ZERO_EXTEND;
      allow_zero = true;
      break;

    case Token::BV_EXTRACT:
      kind  = bitwuzla::Kind::BV_EXTRACT;
      nidxs = 2;
      break;

    case Token::FP_NAN:
    case Token::FP_NEG_INF:
    case Token::FP_NEG_ZERO:
    case Token::FP_POS_INF:
    case Token::FP_POS_ZERO:
    case Token::FP_TO_FP:
    case Token::FP_TO_FP_UNSIGNED: nidxs = 2; break;

    case Token::FP_TO_SBV: kind = bitwuzla::Kind::FP_TO_SBV; break;

    case Token::FP_TO_UBV: kind = bitwuzla::Kind::FP_TO_UBV; break;

    case Token::SYMBOL: {
      assert(d_lexer->has_token());
      const std::string& val = d_lexer->token();
      if (val[0] != 'b' || val[1] != 'v')
      {
        return false;
      }
      std::string v = val.substr(2);
      if (!std::all_of(
              v.begin(), v.end(), [](char c) { return std::isdigit(c); }))
      {
        return error("invalid bit-vector value '" + val + "'");
      }
      d_work_args.push_back(v);
    }
    break;

    default: assert(false);
  }

  for (uint64_t i = 0; i < nidxs; ++i)
  {
    if (!parse_uint64())
    {
      return false;
    }
    if (!allow_zero && peek_uint64_arg() == 0)
    {
      return error("expected non-zero index");
    }
  }

  if (!parse_rpars(1))
  {
    return false;
  }

  if (kind == bitwuzla::Kind::VALUE)
  {
    close_term_scope();
    switch (token_kind)
    {
      case Token::FP_NAN:
      case Token::FP_NEG_INF:
      case Token::FP_NEG_ZERO:
      case Token::FP_POS_INF:
      case Token::FP_POS_ZERO: {
        assert(nargs() == 2);
        uint64_t ssize      = pop_uint64_arg();
        uint64_t esize      = pop_uint64_arg();
        bitwuzla::Sort sort = bitwuzla::mk_fp_sort(esize, ssize);
        if (token_kind == Token::FP_NAN)
        {
          d_work_args.push_back(bitwuzla::mk_fp_nan(sort));
        }
        else if (token_kind == Token::FP_NEG_INF)
        {
          d_work_args.push_back(bitwuzla::mk_fp_neg_inf(sort));
        }
        else if (token_kind == Token::FP_POS_INF)
        {
          d_work_args.push_back(bitwuzla::mk_fp_pos_inf(sort));
        }
        else if (token_kind == Token::FP_NEG_ZERO)
        {
          d_work_args.push_back(bitwuzla::mk_fp_neg_zero(sort));
        }
        else if (token_kind == Token::FP_POS_ZERO)
        {
          d_work_args.push_back(bitwuzla::mk_fp_pos_zero(sort));
        }
      }
      break;

      default: {
        assert(token_kind == Token::SYMBOL);
        assert(nargs() == 2);
        uint64_t size       = pop_uint64_arg();
        std::string val     = pop_str_arg();
        bitwuzla::Sort sort = bitwuzla::mk_bv_sort(size);
        d_work_args.push_back(bitwuzla::mk_bv_value(sort, val, 10));
      }
    }
  }
  else
  {
    // ((_ <indexed_op> <idxs) <terms>) -> (<indexed_op> <idxs> <terms>)
    close_term_scope();
    assert(node);
    d_work.emplace_back(token_kind, node, std::move(coo));
  }
  return true;
}

bool
Parser::parse_open_term_quant()
{
  if (!parse_lpars(1))
  {
    return false;
  }
  open_term_scope();
  d_work.emplace_back(Token::SORTED_VARS, d_lexer->coo());
  assert(!d_is_sorted_var);
  d_is_sorted_var = true;
  return true;
}

bool
Parser::parse_open_term_symbol()
{
  ParsedItem& cur         = d_work.back();
  SymbolTable::Node* node = std::get<SymbolTable::Node*>(cur.d_parsed);
  Token token             = node->d_token;

  if (is_token_class(token, TokenClass::COMMAND))
  {
    return error("unexpected command '" + node->d_symbol + "'");
  }
  if (is_token_class(token, TokenClass::KEYWORD))
  {
    return error("unexpected keyword '" + node->d_symbol + "'");
  }
  if (is_token_class(token, TokenClass::RESERVED))
  {
    if (token == Token::LET)
    {
      d_work.emplace_back(token, d_lexer->coo());
      if (!parse_lpars(1))
      {
        return false;
      }
      open_term_scope();
      d_work.emplace_back(Token::PARLETBIND, d_lexer->coo());
      assert(!d_is_var_binding);
      d_is_var_binding = true;
    }
    else if (token == Token::FORALL || token == Token::EXISTS)
    {
      d_work.emplace_back(token, d_lexer->coo());
      if (!parse_open_term_quant())
      {
        return false;
      }
    }
    else if (token == Token::UNDERSCORE)
    {
      if (!parse_open_term_indexed())
      {
        return false;
      }
    }
    else if (token == Token::AS)
    {
      d_work.emplace_back(token, d_lexer->coo());
      if (!parse_open_term_as())
      {
        return false;
      }
    }
    else if (token != Token::BANG)
    {
      assert(node->has_symbol());
      return error("unsupported reserved word '" + node->d_symbol + "'");
    }
    else
    {
      d_work.emplace_back(token, d_lexer->coo());
    }
  }
  else if (token == Token::SYMBOL)
  {
    if (node->d_term.is_null())
    {
      assert(node->has_symbol());
      return error("undefined symbol '" + node->d_symbol + "'");
    }
    cur.d_token = Token::EXP;
  }
  else if (token == Token::TRUE)
  {
    d_work.pop_back();
    d_work_args.push_back(bitwuzla::mk_true());
  }
  else if (token == Token::FALSE)
  {
    d_work.pop_back();
    d_work_args.push_back(bitwuzla::mk_false());
  }
  else if (token == Token::ATTRIBUTE)
  {
    return error("unexpected attribute '" + std::to_string(token) + "'");
  }
  else if (is_token_class(token, TokenClass::CORE))
  {
    if (token == Token::BOOL)
    {
      return error("unexpected '" + std::to_string(token) + "'");
    }
  }
  else if (d_arrays_enabled && is_token_class(token, TokenClass::ARRAY))
  {
    if (token == Token::ARRAY)
    {
      return error("unexpected '" + std::to_string(token) + "'");
    }
  }
  else if (d_bv_enabled && is_token_class(token, TokenClass::BV))
  {
    if (token == Token::BV_BITVEC)
    {
      return error("unexpected '" + std::to_string(token) + "'");
    }
  }
  else if (d_fp_enabled && is_token_class(token, TokenClass::FP))
  {
    if (token == Token::FP_FLOATINGPOINT || token == Token::FP_FLOAT16
        || token == Token::FP_FLOAT32 || token == Token::FP_FLOAT64
        || token == Token::FP_FLOAT128)
    {
      return error("unexpected '" + std::to_string(token) + "'");
    }

    if (token == Token::FP_RM_RNA_LONG || token == Token::FP_RM_RNA)
    {
      d_work.pop_back();
      d_work_args.push_back(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNA));
    }
    else if (token == Token::FP_RM_RNE_LONG || token == Token::FP_RM_RNE)
    {
      d_work.pop_back();
      d_work_args.push_back(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNE));
    }
    else if (token == Token::FP_RM_RTN_LONG || token == Token::FP_RM_RTN)
    {
      d_work.pop_back();
      d_work_args.push_back(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTN));
    }
    else if (token == Token::FP_RM_RTP_LONG || token == Token::FP_RM_RTP)
    {
      d_work.pop_back();
      d_work_args.push_back(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTP));
    }
    else if (token == Token::FP_RM_RTZ_LONG || token == Token::FP_RM_RTZ)
    {
      d_work.pop_back();
      d_work_args.push_back(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTZ));
    }
  }
  else if (token != Token::REAL_DIV)
  {
    return error("unexpected token '" + std::to_string(token) + "'");
  }
  return true;
}

bool
Parser::close_term(Token token)
{
  uint64_t nopen = d_term_open;
  if (!nopen)
  {
    return error("expected expression");
  }

  assert(d_work.size());
  const ParsedItem& item = d_work.back();

  if (d_expect_body)
  {
    return error("body to '" + std::to_string(item.d_token) + "' missing");
  }

  bool res = false;
  switch (item.d_token)
  {
    case Token::SYMBOL: res = close_term_fun_app(item); break;
    case Token::AS: res = close_term_as(item); break;
    case Token::BANG: res = close_term_bang(item); break;

    case Token::AND:
    case Token::DISTINCT:
    case Token::EQUAL:
    case Token::IMPLIES:
    case Token::ITE:
    case Token::NOT:
    case Token::OR:
    case Token::XOR: res = close_term_core(item); break;

    case Token::ARRAY_SELECT:
    case Token::ARRAY_STORE: res = close_term_array(item); break;

    case Token::BV_ADD:
    case Token::BV_AND:
    case Token::BV_ASHR:
    case Token::BV_COMP:
    case Token::BV_CONCAT:
    case Token::BV_EXTRACT:
    case Token::BV_LSHR:
    case Token::BV_MUL:
    case Token::BV_NAND:
    case Token::BV_NEG:
    case Token::BV_NOR:
    case Token::BV_NOT:
    case Token::BV_OR:
    case Token::BV_REPEAT:
    case Token::BV_ROTATE_LEFT:
    case Token::BV_ROTATE_RIGHT:
    case Token::BV_SDIV:
    case Token::BV_SGE:
    case Token::BV_SGT:
    case Token::BV_SHL:
    case Token::BV_SIGN_EXTEND:
    case Token::BV_SLE:
    case Token::BV_SLT:
    case Token::BV_SMOD:
    case Token::BV_SREM:
    case Token::BV_SUB:
    case Token::BV_UDIV:
    case Token::BV_UGE:
    case Token::BV_UGT:
    case Token::BV_ULE:
    case Token::BV_ULT:
    case Token::BV_UREM:
    case Token::BV_XNOR:
    case Token::BV_XOR:
    case Token::BV_ZERO_EXTEND:
    case Token::BV_REDOR:
    case Token::BV_REDAND:
    case Token::BV_REDXOR:
    case Token::BV_SADDO:
    case Token::BV_UADDO:
    case Token::BV_SDIVO:
    case Token::BV_SMULO:
    case Token::BV_UMULO:
    case Token::BV_SSUBO:
    case Token::BV_USUBO: res = close_term_bv(item); break;

    case Token::FP_ABS:
    case Token::FP_ADD:
    case Token::FP_DIV:
    case Token::FP_EQ:
    case Token::FP_FMA:
    case Token::FP_FP:
    case Token::FP_GEQ:
    case Token::FP_GT:
    case Token::FP_IS_INF:
    case Token::FP_IS_NAN:
    case Token::FP_IS_NEG:
    case Token::FP_IS_NORMAL:
    case Token::FP_IS_POS:
    case Token::FP_IS_SUBNORMAL:
    case Token::FP_IS_ZERO:
    case Token::FP_LEQ:
    case Token::FP_LT:
    case Token::FP_MAX:
    case Token::FP_MIN:
    case Token::FP_MUL:
    case Token::FP_NAN:
    case Token::FP_NEG:
    case Token::FP_NEG_INF:
    case Token::FP_NEG_ZERO:
    case Token::FP_POS_INF:
    case Token::FP_POS_ZERO:
    case Token::FP_REM:
    case Token::FP_RTI:
    case Token::FP_SQRT:
    case Token::FP_SUB:
    case Token::FP_TO_FP:
    case Token::FP_TO_FP_UNSIGNED:
    case Token::FP_TO_SBV:
    case Token::FP_TO_UBV:
    case Token::REAL_DIV: res = close_term_fp(item); break;

    case Token::EXISTS:
    case Token::FORALL: res = close_term_quant(item); break;

    case Token::LET: res = close_term_let(item); break;

    case Token::LETBIND: res = close_term_letbind(item); break;

    case Token::PARLETBIND: res = close_term_parletbind(item); break;

    case Token::SORTED_VAR: res = close_term_sorted_var(item); break;

    case Token::SORTED_VARS: res = close_term_sorted_vars(item); break;

    default:
      return error("unsupported term kind '" + std::to_string(token) + "'");
  }

#if 0
  item_cur = item_open + 1;
  if (item_cur == parser->work.top)
    return !perr_smt2(parser, "unexpected '()'");
  nargs = parser->work.top - item_cur - 1;
  tag   = item_cur->tag;

  /* check if operands are expressions -------------------------------------- */
  if (tag != BZLA_LET_TAG_SMT2 && tag != BZLA_LETBIND_TAG_SMT2
      && tag != BZLA_PARLETBINDING_TAG_SMT2 && tag != BZLA_REAL_DIV_TAG_SMT2
      && tag != BZLA_SORTED_VAR_TAG_SMT2 && tag != BZLA_SORTED_VARS_TAG_SMT2
      && tag != BZLA_FORALL_TAG_SMT2 && tag != BZLA_EXISTS_TAG_SMT2
      && tag != BZLA_BANG_TAG_SMT2)
  {
    i = 1;
    for (; i <= nargs; i++)
    {
      if (item_cur[i].tag != BZLA_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        if (item_cur[i].tag == BZLA_REAL_CONSTANT_TAG_SMT2
            || item_cur[i].tag == BZLA_REAL_DIV_TAG_SMT2)
        {
          if (tag == BZLA_FP_TO_FP_TAG_SMT2) continue;
          return !perr_smt2(parser, "Real constants not supported");
        }
        return !perr_smt2(parser, "expected expression");
      }
    }
  }

  assert(open > 0);
  parser->open = open - 1;

  return 1;
#endif
  if (!parse_rpars(1))
  {
    return false;
  }
  close_term_scope();
  return res;
}

bool
Parser::close_term_as(const ParsedItem& item_open)
{
  if (nargs() != 2)
  {
    return error("expected exactly one term argument to 'as', got '"
                     + std::to_string(nargs() > 0 ? nargs() - 1 : 0) + "'",
                 &item_open.d_coo);
  }
  bitwuzla::Term term = pop_term_arg();
  bitwuzla::Sort sort = pop_sort_arg();
  assert(sort.is_array());
  d_work_args.push_back(bitwuzla::mk_const_array(sort, term));
  return true;
}

bool
Parser::close_term_bang(const ParsedItem& item_open)
{
  if (nargs() != 3)
  {
    return error("invalid annotation syntax, expected 3 arguments, got '"
                     + std::to_string(nargs()) + "'",
                 &item_open.d_coo);
  }
  if (!peek_is_node_arg())
  {
    return error(
        "invalid annotation syntax, expected symbol as third argument");
  }
  SymbolTable::Node* symbol = pop_node_arg();
  if (!peek_is_node_arg())
  {
    return error(
        "invalid annotation syntax, expected ':named' as second argument");
  }
  SymbolTable::Node* named = pop_node_arg();
  if (named->d_token != Token::NAMED)
  {
    return error(
        "invalid annotation syntax, expected ':named' as second argument");
  }
  if (!peek_is_term_arg())
  {
    return error("invalid annotation syntax, expected term as first argument");
  }
  bitwuzla::Term term = pop_term_arg();
  symbol->d_term      = term;
  d_work_args.push_back(term);
  return true;
}

bool
Parser::close_term_array(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  if (token == Token::ARRAY_SELECT)
  {
    if (nargs() != 2)
    {
      return error("expected 2 arguments to '" + std::to_string(token)
                   + "', got '" + std::to_string(nargs()) + "'");
    }
    if (!peek_is_term_arg())
    {
      return error("expected term as second argument to '"
                   + std::to_string(token) + "'");
    }
    bitwuzla::Term index = pop_term_arg();
    if (!peek_is_term_arg())
    {
      return error("expected term as first argument to '"
                   + std::to_string(token) + "'");
    }
    bitwuzla::Term array = pop_term_arg();
    if (!array.sort().is_array())
    {
      return error("expected array as first argument to '"
                   + std::to_string(token) + "'");
    }
    d_work_args.push_back(
        bitwuzla::mk_term(bitwuzla::Kind::ARRAY_SELECT, {array, index}));
    return true;
  }

  assert(item_open.d_token == Token::ARRAY_STORE);
  if (nargs() != 3)
  {
    return error("expected 3 arguments to '" + std::to_string(token)
                 + "', got '" + std::to_string(nargs()) + "'");
  }
  if (!peek_is_term_arg())
  {
    return error("expected term as third argument to '" + std::to_string(token)
                 + "'");
  }
  bitwuzla::Term element = pop_term_arg();
  if (!peek_is_term_arg())
  {
    return error("expected term as second argument to '" + std::to_string(token)
                 + "'");
  }
  bitwuzla::Term index = pop_term_arg();
  if (!peek_is_term_arg())
  {
    return error("expected term as first argument to '" + std::to_string(token)
                 + "'");
  }
  bitwuzla::Term array = pop_term_arg();
  if (!array.sort().is_array())
  {
    return error("expected array as first argument to '" + std::to_string(token)
                 + "'");
  }
  if (index.sort() != array.sort().array_index())
  {
    return error("index sort of array and sort of index do not match");
  }
  if (element.sort() != array.sort().array_element())
  {
    return error("element sort of array and sort of element do not match");
  }
  d_work_args.push_back(
      bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE, {array, index, element}));
  return true;
}

bool
Parser::close_term_core(const ParsedItem& item_open)
{
#if 0
  /* CORE: NOT -------------------------------------------------------------- */
  else if (tag == BZLA_NOT_TAG_SMT2)
  {
    if (nargs != 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser, "'not' with %d arguments but expected exactly one", nargs);
    }
    tmp = item_cur[1].exp;
    if (!bitwuzla_term_is_bool(tmp))
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser, "expected bool");
    }
    parser->work.top = item_cur;
    item_open->tag   = BZLA_EXP_TAG_SMT2;
    item_open->exp   = bitwuzla_mk_term1(BITWUZLA_KIND_NOT, tmp);
  }
  /* CORE: IMPLIES ---------------------------------------------------------- */
  else if (tag == BZLA_IMPLIES_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_IMPLIES))
    {
      return 0;
    }
  }
  /* CORE: AND -------------------------------------------------------------- */
  else if (tag == BZLA_AND_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_AND))
    {
      return 0;
    }
  }
  /* CORE: OR --------------------------------------------------------------- */
  else if (tag == BZLA_OR_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_OR))
    {
      return 0;
    }
  }
  /* CORE: XOR -------------------------------------------------------------- */
  else if (tag == BZLA_XOR_TAG_SMT2)
  {
    if (!close_term_bin_bool(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_XOR))
    {
      return 0;
    }
  }
  /* CORE: EQUAL ------------------------------------------------------------ */
  else if (tag == BZLA_EQUAL_TAG_SMT2)
  {
    if (!nargs)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "arguments to '=' missing");
    }
    if (nargs == 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "only one argument to '='");
    }
    if (!check_arg_sorts_match_smt2(parser, item_cur, 0, nargs)) return 0;
    BitwuzlaTermStack args;
    BZLA_INIT_STACK(parser->mem, args);
    for (uint32_t i = 1; i <= nargs; i++)
      BZLA_PUSH_STACK(args, item_cur[i].exp);
    exp = bitwuzla_mk_term(BITWUZLA_KIND_EQUAL, nargs, args.start);
    BZLA_RELEASE_STACK(args);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* CORE: DISTINCT --------------------------------------------------------- */
  else if (tag == BZLA_DISTINCT_TAG_SMT2)
  {
    if (!nargs)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "arguments to 'distinct' missing");
    }
    if (nargs == 1)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "only one argument to 'distinct'");
    }
    if (!check_arg_sorts_match_smt2(parser, item_cur, 0, nargs)) return 0;
    BitwuzlaTermStack args;
    BZLA_INIT_STACK(parser->mem, args);
    for (uint32_t i = 1; i <= nargs; i++)
      BZLA_PUSH_STACK(args, item_cur[i].exp);
    exp = bitwuzla_mk_term(BITWUZLA_KIND_DISTINCT, nargs, args.start);
    BZLA_RELEASE_STACK(args);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* CORE: ITE -------------------------------------------------------------- */
  else if (tag == BZLA_ITE_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 3)) return 0;
    if (!check_ite_args_sorts_match_smt2(parser, item_cur)) return 0;
    exp = bitwuzla_mk_term3(
        BITWUZLA_KIND_ITE, item_cur[1].exp, item_cur[2].exp, item_cur[3].exp);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
#endif
}

bool
Parser::close_term_bv(const ParsedItem& item_open)
{
#if 0
  /* BV: EXTRACT ------------------------------------------------------------ */
  else if (tag == BZLA_BV_EXTRACT_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
    if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
    width = bitwuzla_term_bv_get_size(item_cur[1].exp);
    if (width <= (uint32_t) item_cur->idx0)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser,
                        "first (high) 'extract' parameter %u too large "
                        "for bit-vector argument of bit-width %u",
                        item_cur->idx0,
                        width);
    }
    exp = bitwuzla_mk_term1_indexed2(BITWUZLA_KIND_BV_EXTRACT,
                                     item_cur[1].exp,
                                     item_cur->idx0,
                                     item_cur->idx1);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* BV: NOT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_NOT_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NOT))
    {
      return 0;
    }
  }
  /* BV: NEG ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_NEG_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NEG))
    {
      return 0;
    }
  }
  /* BV: REDOR -------------------------------------------------------------- */
  else if (tag == BZLA_BV_REDOR_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_REDOR))
    {
      return 0;
    }
  }
  /* BV: REDXOR ------------------------------------------------------------- */
  else if (tag == BZLA_BV_REDXOR_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_REDXOR))
    {
      return 0;
    }
  }
  /* BV: REDAND ------------------------------------------------------------- */
  else if (tag == BZLA_BV_REDAND_TAG_SMT2)
  {
    if (!close_term_unary_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_REDAND))
    {
      return 0;
    }
  }
  /* BV: CONCAT ------------------------------------------------------------- */
  else if (tag == BZLA_BV_CONCAT_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_CONCAT))
    {
      return 0;
    }
  }
  /* BV: AND ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_AND_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_AND))
    {
      return 0;
    }
  }
  /* BV: OR ----------------------------------------------------------------- */
  else if (tag == BZLA_BV_OR_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_OR))
    {
      return 0;
    }
  }
  /* BV: XOR ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_XOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_XOR))
    {
      return 0;
    }
  }
  /* BV: ADD ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_ADD_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ADD))
    {
      return 0;
    }
  }
  /* BV: SUB ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SUB_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SUB))
    {
      return 0;
    }
  }
  /* BV: MUL ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_MUL_TAG_SMT2)
  {
    if (!close_term_bin_bv_left_associative(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_MUL))
    {
      return 0;
    }
  }
  /* BV: UDIV --------------------------------------------------------------- */
  else if (tag == BZLA_BV_UDIV_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UDIV))
    {
      return 0;
    }
  }
  /* BV: UREM --------------------------------------------------------------- */
  else if (tag == BZLA_BV_UREM_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UREM))
    {
      return 0;
    }
  }
  /* BV: SHL ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SHL_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SHL))
    {
      return 0;
    }
  }
  /* BV: LSHR --------------------------------------------------------------- */
  else if (tag == BZLA_BV_LSHR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SHR))
    {
      return 0;
    }
  }
  /* BV: ULT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_ULT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ULT))
    {
      return 0;
    }
  }
  /* BV: NAND --------------------------------------------------------------- */
  else if (tag == BZLA_BV_NAND_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NAND))
    {
      return 0;
    }
  }
  /* BV: NOR ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_NOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_NOR))
    {
      return 0;
    }
  }
  /* BV: XNOR --------------------------------------------------------------- */
  else if (tag == BZLA_BV_XNOR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_XNOR))
    {
      return 0;
    }
  }
  /* BV: COMP --------------------------------------------------------------- */
  else if (tag == BZLA_BV_COMP_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_COMP))
    {
      return 0;
    }
  }
  /* BV: SDIV --------------------------------------------------------------- */
  else if (tag == BZLA_BV_SDIV_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SDIV))
    {
      return 0;
    }
  }
  /* BV: SREM --------------------------------------------------------------- */
  else if (tag == BZLA_BV_SREM_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SREM))
    {
      return 0;
    }
  }
  /* BV: SMOD --------------------------------------------------------------- */
  else if (tag == BZLA_BV_SMOD_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SMOD))
    {
      return 0;
    }
  }
  /* BV: ASHR --------------------------------------------------------------- */
  else if (tag == BZLA_BV_ASHR_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ASHR))
    {
      return 0;
    }
  }
  /* BV: REPEAT ------------------------------------------------------------- */
  else if (tag == BZLA_BV_REPEAT_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 1)) return 0;
    if (!check_bv_args_smt2(parser, item_cur, nargs)) return 0;
    width = bitwuzla_term_bv_get_size(item_cur[1].exp);
    if (item_cur->num && ((uint32_t) (INT32_MAX / item_cur->num) < width))
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(parser, "resulting bit-width of 'repeat' too large");
    }
    exp = bitwuzla_mk_term1_indexed1(
        BITWUZLA_KIND_BV_REPEAT, item_cur[1].exp, item_cur->num);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* BV: ZERO EXTEND -------------------------------------------------------- */
  else if (tag == BZLA_BV_ZERO_EXTEND_TAG_SMT2)
  {
    if (!close_term_extend_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ZERO_EXTEND))
    {
      return 0;
    }
  }
  /* BV: SIGN EXTEND -------------------------------------------------------- */
  else if (tag == BZLA_BV_SIGN_EXTEND_TAG_SMT2)
  {
    if (!close_term_extend_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SIGN_EXTEND))
    {
      return 0;
    }
  }
  /* BV: ROTATE LEFT -------------------------------------------------------- */
  else if (tag == BZLA_BV_ROTATE_LEFT_TAG_SMT2)
  {
    if (!close_term_rotate_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ROLI))
    {
      return 0;
    }
  }
  /* BV: ROTATE RIGHT ------------------------------------------------------- */
  else if (tag == BZLA_BV_ROTATE_RIGHT_TAG_SMT2)
  {
    if (!close_term_rotate_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_RORI))
    {
      return 0;
    }
  }
  /* BV: ULE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_ULE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_ULE))
    {
      return 0;
    }
  }
  /* BV: UGT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_UGT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UGT))
    {
      return 0;
    }
  }
  /* BV: UGE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_UGE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UGE))
    {
      return 0;
    }
  }
  /* BV: SLT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SLT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SLT))
    {
      return 0;
    }
  }
  /* BV: SLE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SLE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SLE))
    {
      return 0;
    }
  }
  /* BV: SGT ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SGT_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SGT))
    {
      return 0;
    }
  }
  /* BV: SGE ---------------------------------------------------------------- */
  else if (tag == BZLA_BV_SGE_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SGE))
    {
      return 0;
    }
  }
  /* BV: SADDO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SADDO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SADD_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: UADDO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_UADDO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UADD_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: SDIVO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SDIVO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SDIV_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: SMULO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SMULO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SMUL_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: UMULO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_UMULO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_UMUL_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: SSUBO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_SSUBO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_SSUB_OVERFLOW))
    {
      return 0;
    }
  }
  /* BV: USUBO -------------------------------------------------------------- */
  else if (tag == BZLA_BV_USUBO_TAG_SMT2)
  {
    if (!close_term_bin_bv_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_BV_USUB_OVERFLOW))
    {
      return 0;
    }
  }
#endif
}

bool
Parser::close_term_fp(const ParsedItem& item_open)
{
#if 0
  /* FP: (fp (_ BitVec 1) (_ BitVec n) (_ BitVec m)) -------------------- */
  else if (tag == BZLA_FP_FP_TAG_SMT2)
  {
    if (nargs < 3)
    {
      parser->perrcoo = item_cur->coo;
      return !perr_smt2(
          parser, "argument to '%s' missing", item_cur->node->name);
    }
    for (i = 1; i <= nargs; i++)
    {
      if (!bitwuzla_term_is_bv(item_cur[i].exp))
      {
        return !perr_smt2(
            parser,
            "invalid argument to '%s', expected bit-vector expression",
            item_cur->node->name);
      }
    }
    if (bitwuzla_term_bv_get_size(item_cur[1].exp) != 1)
      return !perr_smt2(parser,
                        "first argument to '%s' invalid, expected "
                        "bit-vector sort of size 1",
                        item_cur->node->name);
    if (bitwuzla_term_is_bv_value(item_cur[1].exp)
        && bitwuzla_term_is_bv_value(item_cur[2].exp)
        && bitwuzla_term_is_bv_value(item_cur[3].exp))
    {
      exp = bitwuzla_mk_fp_value(
          item_cur[1].exp, item_cur[2].exp, item_cur[3].exp);
    }
    else
    {
      exp = bitwuzla_mk_term3(BITWUZLA_KIND_FP_FP,
                              item_cur[1].exp,
                              item_cur[2].exp,
                              item_cur[3].exp);
    }
    assert(exp);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* FP: fp.abs ------------------------------------------------------------- */
  else if (tag == BZLA_FP_ABS_TAG_SMT2)
  {
    if (!close_term_unary_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_ABS))
    {
      return 0;
    }
  }
  /* FP: fp.neg ------------------------------------------------------------- */
  else if (tag == BZLA_FP_NEG_TAG_SMT2)
  {
    if (!close_term_unary_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_NEG))
    {
      return 0;
    }
  }
  /* FP: fp.sqrt ------------------------------------------------------------ */
  else if (tag == BZLA_FP_SQRT_TAG_SMT2)
  {
    if (!close_term_unary_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_SQRT))
    {
      return 0;
    }
  }
  /* FP: fp.roundToIntegral ------------------------------------------------- */
  else if (tag == BZLA_FP_ROUND_TO_INT_TAG_SMT2)
  {
    if (!close_term_unary_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_RTI))
    {
      return 0;
    }
  }
  /* FP: fp.add ------------------------------------------------------------- */
  else if (tag == BZLA_FP_ADD_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_ADD))
    {
      return 0;
    }
  }
  /* FP: fp.sub ------------------------------------------------------------- */
  else if (tag == BZLA_FP_SUB_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_SUB))
    {
      return 0;
    }
  }
  /* FP: fp.mul ------------------------------------------------------------- */
  else if (tag == BZLA_FP_MUL_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_MUL))
    {
      return 0;
    }
  }
  /* FP: fp.div ------------------------------------------------------------- */
  else if (tag == BZLA_FP_DIV_TAG_SMT2)
  {
    if (!close_term_bin_rm_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_DIV))
    {
      return 0;
    }
  }
  /* FP: fp.fma ------------------------------------------------------------- */
  else if (tag == BZLA_FP_FMA_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 4)) return 0;
    if (!check_rm_fp_args_smt2(parser, item_cur, nargs)) return 0;
    if (!check_arg_sorts_match_smt2(parser, item_cur, 1, 3)) return 0;
    BitwuzlaTerm args[] = {
        item_cur[1].exp, item_cur[2].exp, item_cur[3].exp, item_cur[4].exp};
    exp = bitwuzla_mk_term(BITWUZLA_KIND_FP_FMA, 4, args);
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* FP: fp.rem ------------------------------------------------------------- */
  else if (tag == BZLA_FP_REM_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_REM))
    {
      return 0;
    }
  }
  /* FP: fp.min ------------------------------------------------------------- */
  else if (tag == BZLA_FP_MIN_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_MIN))
    {
      return 0;
    }
  }
  /* FP: fp.max ------------------------------------------------------------- */
  else if (tag == BZLA_FP_MAX_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_MAX))
    {
      return 0;
    }
  }
  /* FP: fp.eq -------------------------------------------------------------- */
  else if (tag == BZLA_FP_EQ_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_EQUAL))
    {
      return 0;
    }
  }
  /* FP: fp.leq ------------------------------------------------------------- */
  else if (tag == BZLA_FP_LEQ_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_LEQ))
    {
      return 0;
    }
  }
  /* FP: fp.lt -------------------------------------------------------------- */
  else if (tag == BZLA_FP_LT_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_LT))
    {
      return 0;
    }
  }
  /* FP: fp.geq ------------------------------------------------------------- */
  else if (tag == BZLA_FP_GEQ_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_GEQ))
    {
      return 0;
    }
  }
  /* FP: fp.gt -------------------------------------------------------------- */
  else if (tag == BZLA_FP_GT_TAG_SMT2)
  {
    if (!close_term_bin_fp_fun_chainable(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_GT))
    {
      return 0;
    }
  }
  /* FP: fp.isNormal -------------------------------------------------------- */
  else if (tag == BZLA_FP_IS_NORMAL_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_NORMAL))
    {
      return 0;
    }
  }
  /* FP: fp.isSubnormal ----------------------------------------------------- */
  else if (tag == BZLA_FP_IS_SUBNORMAL_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_SUBNORMAL))
    {
      return 0;
    }
  }
  /* FP: fp.isZero ---------------------------------------------------------- */
  else if (tag == BZLA_FP_IS_ZERO_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_ZERO))
    {
      return 0;
    }
  }
  /* FP: fp.isInfinite ------------------------------------------------------ */
  else if (tag == BZLA_FP_IS_INF_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_INF))
    {
      return 0;
    }
  }
  /* FP: fp.isNaN ----------------------------------------------------------- */
  else if (tag == BZLA_FP_IS_NAN_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_NAN))
    {
      return 0;
    }
  }
  /* FP: fp.isNegative ------------------------------------------------------ */
  else if (tag == BZLA_FP_IS_NEG_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_NEG))
    {
      return 0;
    }
  }
  /* FP: fp.isPositive ------------------------------------------------------ */
  else if (tag == BZLA_FP_IS_POS_TAG_SMT2)
  {
    if (!close_term_unary_bool_fp_fun(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FP_IS_POS))
    {
      return 0;
    }
  }
  /* FP: fp.to_sbv fp.to_ubv ------------------------------------------------ */
  else if (tag == BZLA_FP_TO_SBV_TAG_SMT2 || tag == BZLA_FP_TO_UBV_TAG_SMT2)
  {
    assert(item_cur->idx0);
    if (item_cur[1].tag != BZLA_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser, "expected expression");
    }
    if (!bitwuzla_term_is_rm(item_cur[1].exp))
    {
      return !perr_smt2(
          parser,
          "invalid argument to '%s', expected bit-vector expression",
          item_cur->node->name);
    }
    if (item_cur[2].tag != BZLA_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "expected expression");
    }
    if (!bitwuzla_term_is_fp(item_cur[2].exp))
    {
      return !perr_smt2(
          parser,
          "invalid argument to '%s', expected bit-vector expression",
          item_cur->node->name);
    }
    if (tag == BZLA_FP_TO_SBV_TAG_SMT2)
    {
      exp = bitwuzla_mk_term2_indexed1(BITWUZLA_KIND_FP_TO_SBV,
                                       item_cur[1].exp,
                                       item_cur[2].exp,
                                       item_cur->idx0);
    }
    else
    {
      exp = bitwuzla_mk_term2_indexed1(BITWUZLA_KIND_FP_TO_UBV,
                                       item_cur[1].exp,
                                       item_cur[2].exp,
                                       item_cur->idx0);
    }
    release_exp_and_overwrite(parser, item_open, item_cur, exp);
  }
  /* FP: to_fp -------------------------------------------------------------- */
  else if (tag == BZLA_FP_TO_FP_TAG_SMT2)
  {
    if (nargs == 1)
    {
      /* (_ to_fp eb sb) (_ BitVec m) */
      if (item_cur[1].tag != BZLA_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[1].coo;
        return !perr_smt2(parser, "expected expression");
      }
      if (!bitwuzla_term_is_bv(item_cur[1].exp))
      {
        return !perr_smt2(
            parser,
            "invalid argument to '%s', expected bit-vector expression",
            item_cur->node->name);
      }
      assert(item_cur->idx0);
      assert(item_cur->idx1);
      exp = bitwuzla_mk_term1_indexed2(BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                       item_cur[1].exp,
                                       item_cur->idx0,
                                       item_cur->idx1);
      release_exp_and_overwrite(parser, item_open, item_cur, exp);
    }
    else
    {
      close_term_to_fp_two_args(parser, item_open, item_cur, nargs);
    }
  }
  /* FP: to_fp_unsigned ----------------------------------------------------- */
  else if (tag == BZLA_FP_TO_FP_UNSIGNED_TAG_SMT2)
  {
    close_term_to_fp_two_args(parser, item_open, item_cur, nargs);
  }
  /* Real: / ---------------------------------------------------------------- */
  else if (tag == BZLA_REAL_DIV_TAG_SMT2)
  {
    if (!check_nargs_smt2(parser, item_cur, nargs, 2)) return 0;
    if (!check_real_arg_smt2(parser, item_cur, 1)) return 0;
    if (!check_real_arg_smt2(parser, item_cur, 2)) return 0;
    parser->work.top   = item_cur;
    item_open->tag     = BZLA_REAL_DIV_TAG_SMT2;
    item_open->node    = item_cur[0].node;
    item_open->strs[0] = item_cur[1].str;
    item_open->strs[1] = item_cur[2].str;
  }
#endif
}

bool
Parser::close_term_fun_app(const ParsedItem& item_open)
{
#if 0
      BitwuzlaTermStack fargs;
      BZLA_INIT_STACK(parser->mem, fargs);

      BitwuzlaTerm fun = item_cur[0].exp;
      if (nargs != bitwuzla_term_fun_get_arity(fun))
      {
        BZLA_RELEASE_STACK(fargs);
        return !perr_smt2(parser, "invalid number of arguments");
      }

      size_t size;
      BitwuzlaSort *domain_sorts =
          bitwuzla_term_fun_get_domain_sorts(fun, &size);

      BZLA_PUSH_STACK(fargs, fun);
      for (i = 1; i <= nargs; i++)
      {
        if (item_cur[i].tag != BZLA_EXP_TAG_SMT2)
        {
          BZLA_RELEASE_STACK(fargs);
          parser->perrcoo = item_cur[i].coo;
          return !perr_smt2(parser, "expected expression");
        }
        BZLA_PUSH_STACK(fargs, item_cur[i].exp);
        assert(i - 1 < size);
        assert(domain_sorts[i - 1]);
        if (!bitwuzla_sort_is_equal(
                domain_sorts[i - 1],
                bitwuzla_term_get_sort(BZLA_PEEK_STACK(fargs, i))))
        {
          BZLA_RELEASE_STACK(fargs);
          return !perr_smt2(parser, "invalid sort for argument %d", i);
        }
      }
      parser->work.top = item_cur;
      item_open->tag   = BZLA_EXP_TAG_SMT2;
      item_open->exp   = bitwuzla_mk_term(
          BITWUZLA_KIND_APPLY, BZLA_COUNT_STACK(fargs), fargs.start);
      BZLA_RELEASE_STACK(fargs);
#endif
}

bool
Parser::close_term_let(const ParsedItem& item_open)
{
#if 0
    for (i = 1; i < nargs; i++)
    {
      if (item_cur[i].tag != BZLA_SYMBOL_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        return !perr_smt2(parser, "expected symbol as argument %d of 'let'", i);
      }
    }
    if (item_cur[nargs].tag != BZLA_SYMBOL_TAG_SMT2)
    {
      if (item_cur[i].tag != BZLA_EXP_TAG_SMT2)
      {
        parser->perrcoo = item_cur[i].coo;
        return !perr_smt2(
            parser, "expected expression as argument %d of 'let'", nargs);
      }
    }
    item_open[0].tag = BZLA_EXP_TAG_SMT2;
    item_open[0].exp = item_cur[nargs].exp;
    for (i = 1; i < nargs; i++)
    {
      assert(item_cur[i].tag == BZLA_SYMBOL_TAG_SMT2);
      sym = item_cur[i].node;
      assert(sym);
      assert(sym->coo.x);
      assert(sym->tag == BZLA_SYMBOL_TAG_SMT2);
      remove_symbol_smt2(parser, sym);
    }
    parser->work.top = item_cur;
#endif
}

bool
Parser::close_term_letbind(const ParsedItem& item_open)
{
#if 0
    assert(item_cur[1].tag == BZLA_SYMBOL_TAG_SMT2);
    if (nargs == 1)
      return !perr_smt2(
          parser, "term to be bound to '%s' missing", item_cur[1].node->name);
    if (nargs > 2)
    {
      parser->perrcoo = item_cur[3].coo;
      return !perr_smt2(
          parser, "second term bound to '%s'", item_cur[1].node->name);
    }
    if (item_cur[2].tag != BZLA_EXP_TAG_SMT2)
    {
      parser->perrcoo = item_cur[2].coo;
      return !perr_smt2(parser, "expected expression in 'let' var binding");
    }
    item_open[0] = item_cur[1];
    assert(!item_open[0].node->exp);
    assert(item_cur[2].tag == BZLA_EXP_TAG_SMT2);
    item_open[0].node->exp = item_cur[2].exp;
    assert(!item_open[0].node->bound);
    item_open[0].node->bound = 1;
    parser->work.top         = item_cur;
    assert(!parser->isvarbinding);
    parser->isvarbinding = true;
#endif
}

bool
Parser::close_term_parletbind(const ParsedItem& item_open)
{
#if 0
    assert(parser->isvarbinding);
    parser->isvarbinding = false;
#ifndef NDEBUG
    for (i = 1; i <= nargs; i++)
      assert(item_cur[i].tag == BZLA_SYMBOL_TAG_SMT2);
#endif
    for (i = 0; i < nargs; i++) item_open[i] = item_cur[i + 1];
    parser->work.top = item_open + nargs;
    assert(!parser->expecting_body);
    parser->expecting_body = "let";
#endif
}

bool
Parser::close_term_quant(const ParsedItem& item_open)
{
#if 0
  /* forall (<sorted_var>+) <term> ------------------------------------------ */
  else if (tag == BZLA_FORALL_TAG_SMT2)
  {
    if (!close_term_quant(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_FORALL))
    {
      return 0;
    }
  }
  /* exists (<sorted_var>+) <term> ------------------------------------------ */
  else if (tag == BZLA_EXISTS_TAG_SMT2)
  {
    if (!close_term_quant(
            parser, item_open, item_cur, nargs, BITWUZLA_KIND_EXISTS))
    {
      return 0;
    }
  }
#endif
}

bool
Parser::close_term_sorted_var(const ParsedItem& item_open)
{
#if 0
    assert(item_cur[1].tag == BZLA_SYMBOL_TAG_SMT2);
    if (nargs != 1)
    {
      parser->perrcoo = item_cur[1].coo;
      return !perr_smt2(parser,
                        "expected only one variable at sorted var '%s'",
                        item_cur[1].node->name);
    }
    parser->work.top = item_cur;
    item_open->tag   = BZLA_SYMBOL_TAG_SMT2;
    item_open->node  = item_cur[1].node;
    assert(bitwuzla_term_is_var(item_open->node->exp));
    assert(!parser->sorted_var);
    parser->sorted_var = 1;
#endif
}

bool
Parser::close_term_sorted_vars(const ParsedItem& item_open)
{
#if 0
    assert(parser->sorted_var);
    parser->sorted_var = 0;
#ifndef NDEBUG
    for (i = 1; i <= nargs; i++)
    {
      assert(item_cur[i].tag == BZLA_SYMBOL_TAG_SMT2);
      assert(bitwuzla_term_is_var(item_cur[i].node->exp));
    }
#endif
    for (i = 0; i < nargs; i++) item_open[i] = item_cur[i + 1];
    parser->work.top = item_open + nargs;
    assert(!parser->expecting_body);
    parser->expecting_body = "quantifier";
#endif
}

/* -------------------------------------------------------------------------- */

bool
Parser::parse_sort()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }

  if (token == Token::BOOL)
  {
    d_work_args.push_back(bitwuzla::mk_bool_sort());
    return true;
  }
  if (token == Token::FP_FLOAT16)
  {
    d_work_args.push_back(bitwuzla::mk_fp_sort(5, 11));
    return true;
  }
  if (token == Token::FP_FLOAT32)
  {
    d_work_args.push_back(bitwuzla::mk_fp_sort(8, 24));
    return true;
  }
  if (token == Token::FP_FLOAT64)
  {
    d_work_args.push_back(bitwuzla::mk_fp_sort(11, 53));
    return true;
  }
  if (token == Token::FP_FLOAT128)
  {
    d_work_args.push_back(bitwuzla::mk_fp_sort(15, 113));
    return true;
  }
  if (token == Token::FP_ROUNDINGMODE)
  {
    d_work_args.push_back(bitwuzla::mk_rm_sort());
    return true;
  }
  if (token == Token::LPAR)
  {
    token = next_token();
    if (!check_token(token))
    {
      return false;
    }
    if (token == Token::ARRAY)
    {
      return parse_sort_array();
    }
    if (token != Token::UNDERSCORE)
    {
      return error("expected '_' or 'Array'");
    }
    return parse_sort_bv_fp();
  }
  if (token == Token::SYMBOL)
  {
    assert(d_lexer->has_token());
    SymbolTable::Node* sort = d_table.find(d_lexer->token());
    if (!sort || sort->d_sort.is_null())
    {
      return error("invalid sort '" + d_lexer->token() + "'");
    }
    d_work_args.push_back(sort->d_sort);
    return true;
  }
  return error("expected '(' or sort keyword");
}

bool
Parser::parse_sort_array()
{
  if (!parse_sort())
  {
    return false;
  }
  bitwuzla::Sort index = pop_sort_arg();
  if (!parse_sort())
  {
    return false;
  }
  bitwuzla::Sort element = pop_sort_arg();
  if (!parse_rpars(1))
  {
    return false;
  }
  d_work_args.push_back(bitwuzla::mk_array_sort(index, element));
  return true;
}

bool
Parser::parse_sort_bv_fp()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }

  if (token == Token::BV_BITVEC)
  {
    if (!parse_uint64())
    {
      return false;
    }
    uint64_t size = pop_uint64_arg();
    if (size == 0)
    {
      return error("invalid bit-vector size '0'");
    }
    if (!parse_rpars(1))
    {
      return false;
    }
    d_work_args.push_back(bitwuzla::mk_bv_sort(size));
    return true;
  }
  if (token == Token::FP_FLOATINGPOINT)
  {
    if (!parse_uint64())
    {
      return false;
    }
    uint64_t esize = pop_uint64_arg();
    if (esize == 0)
    {
      return error("invalid exponent bit-vector size '0'");
    }
    if (!parse_uint64())
    {
      return false;
    }
    uint64_t ssize = pop_uint64_arg();
    if (ssize == 0)
    {
      return error("invalid significand bit-vector size '0'");
    }
    if (!parse_rpars(1))
    {
      return false;
    }
    d_work_args.push_back(bitwuzla::mk_fp_sort(esize, ssize));
    return true;
  }
  return error("expected '" + std::to_string(Token::BV_BITVEC) + "' or '"
               + std::to_string(Token::FP_FLOATINGPOINT) + "'");
}

/* -------------------------------------------------------------------------- */

void
Parser::open_term_scope()
{
  d_work_args_control.push_back(d_work_args.size());
  d_term_open += 1;
}

void
Parser::close_term_scope()
{
  d_work_args_control.pop_back();
  d_term_open -= 1;
}

/* -------------------------------------------------------------------------- */

bool
Parser::error(const std::string& error_msg, const Lexer::Coordinate* coo)
{
  assert(d_lexer);
  if (!coo) coo = &d_lexer->coo();
  d_error = d_infile_name + ":" + std::to_string(coo->col) + ":"
            + std::to_string(coo->line) + ": " + error_msg;
  return false;
}

bool
Parser::error_invalid()
{
  assert(d_lexer);
  assert(d_lexer->error());
  return error(d_lexer->error_msg());
}

bool
Parser::error_eof(Token token)
{
  return error("unexpected end of file after '" + std::to_string(token) + "'",
               &d_lexer->last_coo());
}

bool
Parser::check_token(Token token)
{
  if (token == Token::ENDOFFILE)
  {
    return error_eof(token);
  }
  if (token == Token::INVALID)
  {
    return error_invalid();
  }
  return true;
}

bool
Parser::is_symbol(Token token)
{
  return token == Token::SYMBOL || token == Token::ATTRIBUTE
         || (static_cast<uint32_t>(token) & d_token_class_mask) > 0;
}
size_t
Parser::enable_theory(const std::string& logic,
                      const std::string& theory,
                      size_t size_prefix)
{
  if (size_prefix < logic.size())
  {
    size_t size_theory = theory.size();
    std::string l      = logic.substr(size_prefix, size_theory);
    if (l == theory)
    {
      if (theory == "A")
      {
        d_table.init_array_symbols();
        d_token_class_mask |= static_cast<uint32_t>(TokenClass::ARRAY);
        d_arrays_enabled = true;
      }
      else if (theory == "BV")
      {
        d_table.init_bv_symbols();
        d_token_class_mask |= static_cast<uint32_t>(TokenClass::BV);
        d_bv_enabled = true;
      }
      else if (theory == "FP" || theory == "FPLRA")
      {
        d_table.init_fp_symbols();
        d_token_class_mask |= static_cast<uint32_t>(TokenClass::FP);
        d_token_class_mask |= static_cast<uint32_t>(TokenClass::REALS);
        d_fp_enabled = true;
      }
      size_prefix += size_theory;
    }
  }
  return size_prefix;
}

bool
Parser::is_supported_logic(const std::string& logic)
{
  size_t size = logic.size(), size_prefix = 0;

  if (size < 3)
  {
    return false;
  }

  if (logic == "ALL")
  {
    d_table.init_array_symbols();
    d_table.init_bv_symbols();
    d_table.init_fp_symbols();
    d_token_class_mask |= static_cast<uint32_t>(TokenClass::ARRAY);
    d_token_class_mask |= static_cast<uint32_t>(TokenClass::BV);
    d_token_class_mask |= static_cast<uint32_t>(TokenClass::FP);
    d_token_class_mask |= static_cast<uint32_t>(TokenClass::REALS);
    d_arrays_enabled = true;
    d_bv_enabled     = true;
    d_fp_enabled     = true;
    return true;
  }
  size_prefix = enable_theory(logic, "QF_", size_prefix);
  size_prefix = enable_theory(logic, "A", size_prefix);
  size_prefix = enable_theory(logic, "UF", size_prefix);
  size_prefix = enable_theory(logic, "BV", size_prefix);
  size_prefix = enable_theory(logic, "FPLRA", size_prefix);
  size_prefix = enable_theory(logic, "FP", size_prefix);
  return size_prefix == size;
}

void
Parser::print_success()
{
  if (d_print_success)
  {
    *d_out << "success" << std::endl;
    d_out->flush();
  }
}

/* -------------------------------------------------------------------------- */

size_t
Parser::nargs() const
{
  return d_work_args.size() - d_work_args_control.back();
}

uint64_t
Parser::pop_uint64_arg()
{
  assert(std::holds_alternative<uint64_t>(d_work_args.back()));
  uint64_t res = std::get<uint64_t>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

bitwuzla::Sort
Parser::pop_sort_arg()
{
  assert(std::holds_alternative<bitwuzla::Sort>(d_work_args.back()));
  bitwuzla::Sort res = std::get<bitwuzla::Sort>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

bitwuzla::Term
Parser::pop_term_arg()
{
  assert(std::holds_alternative<bitwuzla::Term>(d_work_args.back()));
  bitwuzla::Term res = std::get<bitwuzla::Term>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

std::string
Parser::pop_str_arg()
{
  assert(std::holds_alternative<std::string>(d_work_args.back()));
  std::string res = std::get<std::string>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

SymbolTable::Node*
Parser::pop_node_arg()
{
  assert(std::holds_alternative<SymbolTable::Node*>(d_work_args.back()));
  SymbolTable::Node* res = std::get<SymbolTable::Node*>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

uint64_t
Parser::peek_uint64_arg() const
{
  assert(std::holds_alternative<uint64_t>(d_work_args.back()));
  return std::get<uint64_t>(d_work_args.back());
}

const bitwuzla::Sort&
Parser::peek_sort_arg() const
{
  assert(std::holds_alternative<bitwuzla::Sort>(d_work_args.back()));
  return std::get<bitwuzla::Sort>(d_work_args.back());
}

SymbolTable::Node*
Parser::peek_node_arg() const
{
  assert(std::holds_alternative<SymbolTable::Node*>(d_work_args.back()));
  return std::get<SymbolTable::Node*>(d_work_args.back());
}

bool
Parser::peek_is_uint64_arg() const
{
  return std::holds_alternative<uint64_t>(d_work_args.back());
}

bool
Parser::peek_is_sort_arg() const
{
  return std::holds_alternative<bitwuzla::Sort>(d_work_args.back());
}

bool
Parser::peek_is_term_arg() const
{
  return std::holds_alternative<bitwuzla::Term>(d_work_args.back());
}

bool
Parser::peek_is_str_arg() const
{
  return std::holds_alternative<std::string>(d_work_args.back());
}

bool
Parser::peek_is_node_arg() const
{
  return std::holds_alternative<SymbolTable::Node*>(d_work_args.back());
}

/* Parser::ParsedItem ------------------------------------------------------- */

Parser::ParsedItem::ParsedItem(Token token, const Lexer::Coordinate& coo)
    : d_token(token), d_coo(coo)
{
}

Parser::ParsedItem::ParsedItem(Token token,
                               const std::string& str,
                               const Lexer::Coordinate& coo)
    : d_token(token), d_parsed(str), d_coo(coo)
{
}

Parser::ParsedItem::ParsedItem(Token token,
                               SymbolTable::Node* node,
                               const Lexer::Coordinate& coo)
    : d_token(token), d_parsed(node), d_coo(coo)
{
}

/* Parser::Statistics ------------------------------------------------------- */

Parser::Statistics::Statistics()
    : num_assertions(d_stats.new_stat<uint64_t>("parser::smt2:num_assertions")),
      num_check_sat(d_stats.new_stat<uint64_t>("parser::smt2:num_check_sat")),
      num_commands(d_stats.new_stat<uint64_t>("parser::smt2:num_commands")),
      num_exit(d_stats.new_stat<uint64_t>("parser::smt2:num_exit")),
      num_set_logic(d_stats.new_stat<uint64_t>("parser::smt2:num_set_logic")),
      time_parse(
          d_stats.new_stat<util::TimerStatistic>("parser::smt2::time_parse"))
{
}

}  // namespace parser::smt2
}  // namespace bzla
