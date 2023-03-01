#include "parser/smt2/parser.h"

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
    assert(!d_lexer->token().empty());
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
    assert(!d_lexer->token().empty());
    error("expected '(' at '" + d_lexer->token() + "'");
    return false;
  }

  token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (!is_token_class(token, TokenClass::COMMAND))
  {
    assert(!d_lexer->token().empty());
    error("expected command at '" + d_lexer->token() + "'");
    return false;
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
      assert(!d_lexer->token().empty());
      error("unsupported command '" + d_lexer->token() + "'");
      return false;
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
    error("missing keyword after 'set-info'");
    return false;
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
      error("invalid value for ':status'");
      return false;
    }
    assert(!d_lexer->token().empty());
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
      error("invalid value '" + status + "' for ':status'");
      return false;
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
  SymbolTable::Node* logic = parse_symbol(" after 'set-logic'");
  if (logic == nullptr)
  {
    return false;
  }
  d_logic = logic->d_symbol;
  assert(!d_logic.empty());
  if (!is_supported_logic(d_logic))
  {
    error("unsupported logic '" + d_logic + "'");
    return false;
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
    error("missing keyword after 'set-option'");
    return false;
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
      error("cannot create '" + outfile_name + "'");
      return false;
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
      assert(!d_lexer->token().empty());
      error("expected Boolean argument at '" + d_lexer->token() + "'");
      return false;
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
      assert(!d_lexer->token().empty());
      error("expected Boolean argument at '" + d_lexer->token() + "'");
      return false;
    }
  }
  else if (token == Token::PRODUCE_UNSAT_ASSUMPTIONS)
  {
    // nothing to do, always true
  }
  // Bitwuzla options
  else
  {
    assert(!d_lexer->token().empty());
    std::string opt = d_lexer->token();
    token           = next_token();
    if (!check_token(token))
    {
      return false;
    }
    assert(!d_lexer->token().empty());
    try
    {
      d_options.set(opt, d_lexer->token());
    }
    catch (bitwuzla::Exception& e)
    {
      error(e.msg());
      return false;
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
Parser::parse_rpars(uint64_t nrpars)
{
  while (nrpars > 0)
  {
    Token token = next_token();
    if (token == Token::ENDOFFILE)
    {
      if (nrpars > 0)
      {
        error("missing ')' at end of file");
        return false;
      }
      return true;
    }
    if (token != Token::RPAR)
    {
      error("missing ')'");
      return false;
    }
    nrpars -= 1;
  }
  return true;
}

SymbolTable::Node*
Parser::parse_symbol(const std::string& error_msg)
{
  Token token = next_token();
  if (!check_token(token))
  {
    return nullptr;
  }
  if (token != Token::SYMBOL)
  {
    error("expected symbol" + error_msg + " but reached end of file");
  }
  assert(d_last_node->d_token == Token::SYMBOL);
  return d_last_node;
}

/* -------------------------------------------------------------------------- */

void
Parser::error(const std::string& error_msg, const Lexer::Coordinate* coo)
{
  assert(d_lexer);
  if (!coo) coo = &d_lexer->coo();
  d_error = d_infile_name + ":" + std::to_string(coo->col) + ":"
            + std::to_string(coo->line) + ": " + error_msg;
}

void
Parser::error_invalid()
{
  assert(d_lexer);
  assert(d_lexer->error());
  error(d_lexer->error_msg());
}

void
Parser::error_eof(Token token)
{
  error("unexpected end of file after '" + std::to_string(token) + "'",
        &d_lexer->last_coo());
}

bool
Parser::check_token(Token token)
{
  if (token == Token::ENDOFFILE)
  {
    error_eof(token);
    return false;
  }
  if (token == Token::INVALID)
  {
    error_invalid();
    return false;
  }
  return true;
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
      }
      else if (theory == "BV")
      {
        d_table.init_bv_symbols();
      }
      else if (theory == "FP" || theory == "FPLRA")
      {
        d_table.init_fp_symbols();
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
