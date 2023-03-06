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
      d_infile_name(infile_name),
      d_lexer(new Lexer(infile)),
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

void
Parser::init_bitwuzla()
{
  if (!d_bitwuzla)
  {
    d_bitwuzla.reset(new bitwuzla::Bitwuzla(d_options));
  }
}

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
      node = d_table.insert(token, d_lexer->token(), d_scope_level);
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
    case Token::CHECK_SAT_ASSUMING: return parse_command_check_sat(true);
    case Token::DECLARE_CONST: return parse_command_declare_fun(true);
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
  init_bitwuzla();
  if (!parse_term())
  {
    return false;
  }
  bitwuzla::Term term = pop_term_arg();
  if (!term.sort().is_bool())
  {
    return error("asserted term is not a formula");
  }
  if (!parse_rpars(1))
  {
    return false;
  }
  d_bitwuzla->assert_formula(term);
  d_statistics.num_commands += 1;
  print_success();
  return true;
}

bool
Parser::parse_command_check_sat(bool with_assumptions)
{
  init_bitwuzla();
  if (!parse_rpars(1))
  {
    return false;
  }
  if (d_statistics.num_commands
      && !d_options.get(bitwuzla::Option::INCREMENTAL))
  {
    return error("incremental solving not enabled");
  }
  d_statistics.num_commands += 1;
  Msg(1) << "parsed " << d_statistics.num_commands << " commands in "
         << d_statistics.time_parse.elapsed() << " seconds";
  if (with_assumptions)
  {
    if (!parse_lpars(1))
    {
      return false;
    }
    if (!parse_term_list())
    {
      return false;
    }
    std::vector<bitwuzla::Term> assumptions;
    assumptions.reserve(nargs());
    for (size_t i = 0, n = nargs(); i < n; ++i)
    {
      size_t idx       = n - i - 1;
      assumptions[idx] = pop_term_arg();
      if (!assumptions[idx].sort().is_bool())
      {
        return error("assumption at index " + std::to_string(idx)
                     + " is not a formula");
      }
    }
    d_result = d_bitwuzla->check_sat(assumptions);
  }
  else
  {
    d_result = d_bitwuzla->check_sat();
  }
  d_statistics.num_check_sat += 1;
  if (d_result == bitwuzla::Result::SAT)
  {
    (*d_out) << "sat" << std::endl;
    if (d_status == bitwuzla::Result::UNSAT)
    {
      return error("'sat' but status is 'unsat'");
    }
  }
  else if (d_result == bitwuzla::Result::UNSAT)
  {
    (*d_out) << "unsat" << std::endl;
    if (d_status == bitwuzla::Result::SAT)
    {
      return error("'unsat' but status is 'sat'");
    }
  }
  else
  {
    // TODO: do not print unknown when printing DIMACS
    (*d_out) << "unknown" << std::endl;
  }
  d_out->flush();
  if (!parse_rpars(1))
  {
    return false;
  }
  if (!d_options.get(bitwuzla::Option::INCREMENTAL))
  {
    d_done = true;
  }
  return true;
}

bool
Parser::parse_command_declare_fun(bool is_const)
{
  if (!parse_symbol(is_const ? "after 'declare-const'" : "after 'declare-fun'"))
  {
    return false;
  }
  assert(nargs() == 1);
  SymbolTable::Node* symbol = pop_node_arg();
  if (symbol->d_coo.line)
  {
    return error("symbol '" + symbol->d_symbol + "' alread defined at line "
                 + std::to_string(symbol->d_coo.line) + " column "
                 + std::to_string(symbol->d_coo.col));
  }
  symbol->d_coo = d_lexer->coo();

  std::vector<bitwuzla::Sort> domain;
  if (!is_const)
  {
    if (!parse_lpars(1))
    {
      return false;
    }
    Token la;
    do
    {
      la = next_token();
      if (!parse_sort(true, la))
      {
        return false;
      }
    } while (la != Token::RPAR);
    domain.reserve(nargs());
    for (size_t i = 0, n = nargs(); i < n; ++i)
    {
      size_t idx  = n - i - 1;
      domain[idx] = pop_sort_arg();
    }
  }

  if (!parse_sort())
  {
    return false;
  }
  bitwuzla::Sort sort = pop_sort_arg();

  if (domain.size())
  {
    symbol->d_term = bitwuzla::mk_const(bitwuzla::mk_fun_sort(domain, sort),
                                        symbol->d_symbol);
  }
  else
  {
    symbol->d_term = bitwuzla::mk_const(sort, symbol->d_symbol);
  }
  if (!parse_rpars(1))
  {
    return false;
  }
  print_success();
  return true;
}

bool
Parser::parse_command_declare_sort()
{
  if (!parse_symbol("after 'declare-sort'"))
  {
    return false;
  }
  assert(nargs() == 1);
  SymbolTable::Node* symbol = pop_node_arg();
  if (symbol->d_coo.line)
  {
    return error("symbol '" + symbol->d_symbol + "' alread defined at line "
                 + std::to_string(symbol->d_coo.line) + " column "
                 + std::to_string(symbol->d_coo.col));
  }
  symbol->d_coo = d_lexer->coo();
  if (!parse_uint64())
  {
    return false;
  }
  if (pop_uint64_arg() != 0)
  {
    return error("'declare-sort' of arity > 0 not supported");
  }
  symbol->d_sort = bitwuzla::mk_uninterpreted_sort(symbol->d_symbol);
  symbol->d_coo  = d_lexer->coo();
  if (!parse_rpars(1))
  {
    return false;
  }
  print_success();
  return true;
}

bool
Parser::parse_command_define_fun()
{
  if (!parse_symbol("after 'define-fun'"))
  {
    return false;
  }
  assert(nargs() == 1);
  SymbolTable::Node* symbol = pop_node_arg();
  if (symbol->d_coo.line)
  {
    return error("symbol '" + symbol->d_symbol + "' alread defined at line "
                 + std::to_string(symbol->d_coo.line) + " column "
                 + std::to_string(symbol->d_coo.col));
  }
  symbol->d_coo = d_lexer->coo();

  if (!parse_lpars(1))
  {
    return false;
  }

  std::vector<bitwuzla::Term> args;
  Token la;
  do
  {
    la = next_token();
    if (!parse_symbol("in sorted var", true, true, la))
    {
      return false;
    }
    SymbolTable::Node* symbol = peek_node_arg();
    if (!parse_sort())
    {
      return false;
    }
    symbol->d_term = bitwuzla::mk_var(pop_sort_arg(), symbol->d_symbol);
    args.push_back(symbol->d_term);
  } while (la != Token::RPAR);

  if (!parse_sort())
  {
    return false;
  }
  bitwuzla::Sort sort = pop_sort_arg();

  if (!parse_term())
  {
    return false;
  }

  bitwuzla::Term body = pop_term_arg();
  if (body.sort() != sort)
  {
    return error("expected term of sort '" + sort.str() + "' but got '"
                 + body.sort().str());
  }

  if (args.size())
  {
    args.push_back(body);
    symbol->d_term = bitwuzla::mk_term(bitwuzla::Kind::LAMBDA, args);
  }
  else
  {
    symbol->d_term = body;
  }

  for (size_t i = 0, n = nargs(); i < n; ++i)
  {
    d_table.remove(pop_node_arg());
  }

  if (!parse_rpars(1))
  {
    return false;
  }
  print_success();
  return true;
}

bool
Parser::parse_command_define_sort()
{
  if (!parse_symbol("after 'define-sort'"))
  {
    return false;
  }
  assert(nargs() == 1);
  SymbolTable::Node* symbol = pop_node_arg();
  if (symbol->d_coo.line)
  {
    return error("symbol '" + symbol->d_symbol + "' alread defined at line "
                 + std::to_string(symbol->d_coo.line) + " column "
                 + std::to_string(symbol->d_coo.col));
  }
  symbol->d_coo = d_lexer->coo();

  if (!parse_lpars(1))
  {
    return false;
  }
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (token != Token::LPAR)
  {
    return error("parameterized 'define-sort' not supported, expected ')'");
  }

  if (!parse_sort())
  {
    return false;
  }
  symbol->d_sort = pop_sort_arg();

  if (!parse_rpars(1))
  {
    return false;
  }
  print_success();
  return true;
}

bool
Parser::parse_command_echo()
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (token != Token::STRING_VALUE)
  {
    return error("expected string after 'echo'");
  }

  assert(d_lexer->has_token());
  std::string echo = d_lexer->token();

  if (!parse_rpars(1))
  {
    return false;
  }

  (*d_out) << echo;
  d_out->flush();

  return true;
}

bool
Parser::parse_command_exit()
{
  if (!parse_rpars(1))
  {
    return false;
  }
  assert(!d_statistics.num_exit);
  d_statistics.num_exit += 1;
  d_done = true;
  print_success();
  return true;
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
  init_bitwuzla();

  if (!parse_uint64())
  {
    return false;
  }
  if (!parse_rpars(1))
  {
    return false;
  }
  uint64_t nlevels = pop_uint64_arg();
  if (nlevels > d_scope_level)
  {
    return error("attempting to pop '" + std::to_string(nlevels)
                 + "' but only '" + std::to_string(nlevels)
                 + "' have been pushed previously");
  }

  if (!d_global_decl)
  {
    // remove symbols from current scope
    for (size_t i = 0; i < nlevels; ++i)
    {
      d_table.pop_scope(d_scope_level);
      d_scope_level -= 1;
    }
  }
  d_bitwuzla->pop(nlevels);
  print_success();
  return true;
}

bool
Parser::parse_command_push()
{
  init_bitwuzla();

  if (!parse_uint64())
  {
    return false;
  }
  if (!parse_rpars(1))
  {
    return false;
  }
  uint64_t nlevels = pop_uint64_arg();
  d_scope_level += nlevels;
  d_bitwuzla->push(nlevels);
  print_success();
  return true;
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
Parser::parse_symbol(const std::string& error_msg,
                     bool shadow,
                     bool look_ahead,
                     Token la)
{
  Token token = look_ahead ? la : next_token();
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
    d_last_node        = d_table.insert(token, d_lexer->token(), d_scope_level);
    d_last_node->d_coo = d_lexer->coo();
  }
  d_work_args.push_back(d_last_node);
  return true;
}

/* -------------------------------------------------------------------------- */

bool
Parser::parse_term(bool look_ahead, Token la)
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
      token      = la;
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
Parser::parse_term_list()
{
  for (;;)
  {
    Token la = next_token();
    if (!check_token(la))
    {
      return false;
    }
    if (la == Token::RPAR)
    {
      break;
    }
    if (!parse_term(true, la))
    {
      return false;
    }
  }
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
    d_work_args.push_back(d_lexer->token());
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
  std::vector<bitwuzla::Term> args;
  if (token == Token::ARRAY_SELECT)
  {
    if (!pop_args(item_open, 2, args))
    {
      return false;
    }
    if (!args[0].sort().is_array())
    {
      return error(
          "expected array as first argument to '" + std::to_string(token) + "'",
          &item_open.d_coo);
    }
    d_work_args.push_back(
        bitwuzla::mk_term(bitwuzla::Kind::ARRAY_SELECT, {args[0], args[1]}));
    return true;
  }

  assert(item_open.d_token == Token::ARRAY_STORE);
  if (!pop_args(item_open, 3, args))
  {
    return false;
  }
  if (!args[0].sort().is_array())
  {
    return error(
        "expected array as first argument to '" + std::to_string(token) + "'",
        &item_open.d_coo);
  }
  if (args[1].sort() != args[0].sort().array_index())
  {
    return error("index sort of array and sort of index do not match",
                 &item_open.d_coo);
  }
  if (args[2].sort() != args[0].sort().array_element())
  {
    return error("element sort of array and sort of element do not match",
                 &item_open.d_coo);
  }
  d_work_args.push_back(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE, args));
  return true;
}

bool
Parser::close_term_core(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  std::vector<bitwuzla::Term> args;
  size_t nexp = 0;
  bitwuzla::Kind kind;

  switch (token)
  {
    case Token::AND:
      nexp = 0;
      kind = bitwuzla::Kind::AND;
      break;
    case Token::DISTINCT:
      nexp = 0;
      kind = bitwuzla::Kind::DISTINCT;
      break;
    case Token::EQUAL:
      nexp = 0;
      kind = bitwuzla::Kind::EQUAL;
      break;
    case Token::IMPLIES:
      nexp = 0;
      kind = bitwuzla::Kind::IMPLIES;
      break;
    case Token::ITE:
      nexp = 3;
      kind = bitwuzla::Kind::ITE;
      break;
    case Token::NOT:
      nexp = 1;
      kind = bitwuzla::Kind::NOT;
      break;
    case Token::OR:
      nexp = 0;
      kind = bitwuzla::Kind::OR;
      break;
    case Token::XOR:
      nexp = 0;
      kind = bitwuzla::Kind::XOR;
      break;
    default: assert(false);
  }
  if (!pop_args(item_open, nexp, args))
  {
    return false;
  }
  if (token == Token::ITE)
  {
    if (!args[0].sort().is_bool())
    {
      return error("expected Boolean term at index 0 as argument to '"
                       + std::to_string(token) + "'",
                   &item_open.d_coo);
    }
    if (args[1].sort() != args[2].sort())
    {
      return error(
          "expected terms of same sort at indices 1 and 2 as argument to '"
              + std::to_string(token) + "'",
          &item_open.d_coo);
    }
  }
  else
  {
    for (size_t i = 0, n = args.size(); i < n; ++i)
    {
      if (!args[i].sort().is_bool())
      {
        return error("expected Boolean term at index " + std::to_string(i)
                         + " as argument to '" + std::to_string(token) + "'",
                     &item_open.d_coo);
      }
    }
  }
  d_work_args.push_back(bitwuzla::mk_term(kind, args));
  return true;
}

bool
Parser::close_term_bv(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> idxs;
  size_t nexp = 0, nidxs = 0;
  bitwuzla::Kind kind;

  switch (token)
  {
    case Token::BV_ADD:
      nexp = 0;
      kind = bitwuzla::Kind::BV_ADD;
      break;
    case Token::BV_AND:
      nexp = 0;
      kind = bitwuzla::Kind::BV_AND;
      break;
    case Token::BV_ASHR:
      nexp = 2;
      kind = bitwuzla::Kind::BV_ASHR;
      break;
    case Token::BV_COMP:
      nexp = 2;
      kind = bitwuzla::Kind::BV_COMP;
      break;
    case Token::BV_CONCAT:
      nexp = 0;
      kind = bitwuzla::Kind::BV_CONCAT;
      break;
    case Token::BV_EXTRACT:
      nexp  = 1;
      nidxs = 2;
      kind  = bitwuzla::Kind::BV_EXTRACT;
      break;
    case Token::BV_LSHR:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SHR;
      break;
    case Token::BV_MUL:
      nexp = 0;
      kind = bitwuzla::Kind::BV_MUL;
      break;
    case Token::BV_NAND:
      nexp = 2;
      kind = bitwuzla::Kind::BV_NAND;
      break;
    case Token::BV_NEG:
      nexp = 1;
      kind = bitwuzla::Kind::BV_NEG;
      break;
    case Token::BV_NOR:
      nexp = 2;
      kind = bitwuzla::Kind::BV_NOR;
      break;
    case Token::BV_NOT:
      nexp = 1;
      kind = bitwuzla::Kind::BV_NOT;
      break;
    case Token::BV_OR:
      nexp = 0;
      kind = bitwuzla::Kind::BV_OR;
      break;
    case Token::BV_REPEAT:
      nexp  = 1;
      nidxs = 1;
      kind  = bitwuzla::Kind::BV_REPEAT;
      break;
    case Token::BV_ROTATE_LEFT:
      nexp  = 1;
      nidxs = 1;
      kind  = bitwuzla::Kind::BV_ROLI;
      break;
    case Token::BV_ROTATE_RIGHT:
      nexp  = 1;
      nidxs = 1;
      kind  = bitwuzla::Kind::BV_RORI;
      break;
    case Token::BV_SDIV:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SDIV;
      break;
    case Token::BV_SGE:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SGE;
      break;
    case Token::BV_SGT:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SGT;
      break;
    case Token::BV_SHL:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SHL;
      break;
    case Token::BV_SIGN_EXTEND:
      nexp  = 1;
      nidxs = 1;
      kind  = bitwuzla::Kind::BV_SIGN_EXTEND;
      break;
    case Token::BV_SLE:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SLE;
      break;
    case Token::BV_SLT:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SLT;
      break;
    case Token::BV_SMOD:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SMOD;
      break;
    case Token::BV_SREM:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SREM;
      break;
    case Token::BV_SUB:
      nexp = 0;
      kind = bitwuzla::Kind::BV_SUB;
      break;
    case Token::BV_UDIV:
      nexp = 2;
      kind = bitwuzla::Kind::BV_UDIV;
      break;
    case Token::BV_UGE:
      nexp = 2;
      kind = bitwuzla::Kind::BV_UGE;
      break;
    case Token::BV_UGT:
      nexp = 2;
      kind = bitwuzla::Kind::BV_UGT;
      break;
    case Token::BV_ULE:
      nexp = 2;
      kind = bitwuzla::Kind::BV_ULE;
      break;
    case Token::BV_ULT:
      nexp = 2;
      kind = bitwuzla::Kind::BV_ULT;
      break;
    case Token::BV_UREM:
      nexp = 2;
      kind = bitwuzla::Kind::BV_UREM;
      break;
    case Token::BV_XNOR:
      nexp = 2;
      kind = bitwuzla::Kind::BV_XNOR;
      break;
    case Token::BV_XOR:
      nexp = 0;
      kind = bitwuzla::Kind::BV_XOR;
      break;
    case Token::BV_ZERO_EXTEND:
      nexp  = 1;
      nidxs = 1;
      kind  = bitwuzla::Kind::BV_ZERO_EXTEND;
      break;
    case Token::BV_REDOR:
      nexp = 1;
      kind = bitwuzla::Kind::BV_REDOR;
      break;
    case Token::BV_REDAND:
      nexp = 1;
      kind = bitwuzla::Kind::BV_REDAND;
      break;
    case Token::BV_REDXOR:
      nexp = 1;
      kind = bitwuzla::Kind::BV_REDXOR;
      break;
    case Token::BV_SADDO:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SADD_OVERFLOW;
      break;
    case Token::BV_UADDO:
      nexp = 2;
      kind = bitwuzla::Kind::BV_UADD_OVERFLOW;
      break;
    case Token::BV_SDIVO:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SDIV_OVERFLOW;
      break;
    case Token::BV_SMULO:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SMUL_OVERFLOW;
      break;
    case Token::BV_UMULO:
      nexp = 2;
      kind = bitwuzla::Kind::BV_UMUL_OVERFLOW;
      break;
    case Token::BV_SSUBO:
      nexp = 2;
      kind = bitwuzla::Kind::BV_SSUB_OVERFLOW;
      break;
    case Token::BV_USUBO:
      nexp = 2;
      kind = bitwuzla::Kind::BV_USUB_OVERFLOW;
      break;
    default: assert(false);
  }
  if (!pop_args(item_open, nexp, args, nidxs, &idxs))
  {
    return false;
  }
  assert(args.size());
  for (size_t i = 0, n = args.size(); i < n; ++i)
  {
    if (!args[i].sort().is_bv())
    {
      return error("expected bit-vector term at index " + std::to_string(i)
                       + " as argument to '" + std::to_string(token) + "'",
                   &item_open.d_coo);
    }
    if (i > 0)
    {
      if (args[i].sort() != args[i - 1].sort())
      {
        return error("expected terms of same sort at indices "
                         + std::to_string(i - 1) + " and " + std::to_string(i)
                         + " as argument to '" + std::to_string(token) + "'",
                     &item_open.d_coo);
      }
    }
  }
  if (token == Token::BV_EXTRACT)
  {
    if (idxs[0] < idxs[1])
    {
      return error("upper index must be >= lower index as argument to '"
                   + std::to_string(token) + "'");
    }
  }
  d_work_args.push_back(bitwuzla::mk_term(kind, args, idxs));
  return true;
}

bool
Parser::close_term_fp(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> idxs;
  size_t nexp = 0, nidxs = 0;
  bool has_rm = false;
  bitwuzla::Kind kind;

  if (token == Token::FP_TO_FP)
  {
    if (!nargs() || nargs() > 2)
    {
      return error("expected 1 or 2 arguments to '"
                       + std::to_string(item_open.d_token) + "', got '"
                       + std::to_string(nargs()) + "'",
                   &item_open.d_coo);
    }
    if (nargs() == 1)
    {
      // ((_ to_fp eb sb) (_ BitVec m))
      if (!pop_args(item_open, 3, args, 2, &idxs))
      {
        return false;
      }
      assert(args.size() == 1);
      assert(idxs.size() == 2);
      if (!args[0].sort().is_bv())
      {
        return error("expected bit-vector term at index 0 as argument to '"
                         + std::to_string(token) + "'",
                     &item_open.d_coo);
      }
      if (args[0].sort().bv_size() != idxs[0] + idxs[1])
      {
        return error("size of bit-vector term '"
                     + std::to_string(args[0].sort().bv_size())
                     + " does not match floating-point format '"
                     + std::to_string(idxs[0]) + " " + std::to_string(idxs[1])
                     + "'");
      }
      d_work_args.push_back(
          bitwuzla::mk_term(bitwuzla::Kind::FP_TO_FP_FROM_BV, args, idxs));
      return true;
    }

    // ((_ to_fp eb sb) RoundingMode (_ FloatingPoint eb sb))
    // ((_ to_fp eb sb) RoundingMode (_ BitVec m))
    // ((_ to_fp eb sb) RoundingMode Real)
    idxs.reserve(2);
    if (peek_is_str_arg())
    {
      std::string s0, s1 = pop_str_arg();
      if (peek_is_str_arg())
      {
        s0 = pop_str_arg();
      }
      if (!peek_is_term_arg())
      {
        return error("expected term as argument at index 0 to '"
                         + std::to_string(item_open.d_token) + "'",
                     &item_open.d_coo);
      }
      bitwuzla::Term rm = pop_term_arg();
      if (!rm.sort().is_rm())
      {
        return error("expected rounding-mode term at index 0 as argument to '"
                         + std::to_string(token) + "'",
                     &item_open.d_coo);
      }
      if (!peek_is_uint64_arg())
      {
        error("expected integer as index to '"
                  + std::to_string(item_open.d_token) + "'",
              &item_open.d_coo);
      }
      idxs[1] = pop_uint64_arg();
      if (!peek_is_uint64_arg())
      {
        error("expected integer as index to '"
                  + std::to_string(item_open.d_token) + "'",
              &item_open.d_coo);
      }
      idxs[0] = pop_uint64_arg();
      if (s0.empty())
      {
        d_work_args.push_back(bitwuzla::mk_fp_value(
            bitwuzla::mk_fp_sort(idxs[0], idxs[1]), rm, s1));
      }
      else
      {
        d_work_args.push_back(bitwuzla::mk_fp_value(
            bitwuzla::mk_fp_sort(idxs[0], idxs[1]), rm, s0, s1));
      }
    }
    else
    {
      if (!peek_is_uint64_arg())
      {
        error("expected integer as index to '"
                  + std::to_string(item_open.d_token) + "'",
              &item_open.d_coo);
      }
      idxs[1] = pop_uint64_arg();
      if (!peek_is_uint64_arg())
      {
        error("expected integer as index to '"
                  + std::to_string(item_open.d_token) + "'",
              &item_open.d_coo);
      }
      idxs[0] = pop_uint64_arg();
      if (!peek_is_term_arg())
      {
        return error("expected term as argument at index 1 to '"
                         + std::to_string(item_open.d_token) + "'",
                     &item_open.d_coo);
      }
      bitwuzla::Term term = pop_term_arg();
      if (!peek_is_term_arg())
      {
        return error("expected term as argument at index 0 to '"
                         + std::to_string(item_open.d_token) + "'",
                     &item_open.d_coo);
      }
      bitwuzla::Term rm = pop_term_arg();
      if (!term.sort().is_bv() && !term.sort().is_fp())
      {
        return error(
            "expected bit-vector or floating-point term at index 1 as argument "
            "to '"
                + std::to_string(token) + "'",
            &item_open.d_coo);
      }
      if (!rm.sort().is_rm())
      {
        return error("expected rounding-mode term at index 0 as argument to '"
                         + std::to_string(token) + "'",
                     &item_open.d_coo);
      }
      d_work_args.push_back(bitwuzla::mk_term(
          term.sort().is_bv() ? bitwuzla::Kind::FP_TO_FP_FROM_UBV
                              : bitwuzla::Kind::FP_TO_FP_FROM_FP,
          {rm, term},
          idxs));
    }
    return true;
  }
  if (token == Token::REAL_DIV)
  {
    if (nargs() != 2)
    {
      return error("expected 2 arguments to '"
                       + std::to_string(item_open.d_token) + "', got '"
                       + std::to_string(nargs()) + "'",
                   &item_open.d_coo);
    }
    if (!peek_is_str_arg())
    {
      return error(
          "expected string representation of denominator as argument to '"
              + std::to_string(item_open.d_token) + "'",
          &item_open.d_coo);
    }
    if (!std::holds_alternative<std::string>(
            d_work_args[d_work_args.size() - 2]))
    {
      return error(
          "expected string representation of denominator as argument to '"
              + std::to_string(item_open.d_token) + "'",
          &item_open.d_coo);
    }
    // nothing to do, we leave the strings on the args stack and only close
    // the current term
    return true;
  }

  switch (token)
  {
    case Token::FP_ABS:
      nexp = 1;
      kind = bitwuzla::Kind::FP_ABS;
      break;
    case Token::FP_ADD:
      nexp   = 3;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_ADD;
      break;
    case Token::FP_DIV:
      nexp   = 3;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_DIV;
      break;
    case Token::FP_EQ:
      nexp = 0;
      kind = bitwuzla::Kind::FP_EQUAL;
      break;
    case Token::FP_FMA:
      nexp   = 4;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_FMA;
      break;
    case Token::FP_FP:
      nexp = 3;
      kind = bitwuzla::Kind::FP_FP;
      break;
    case Token::FP_GEQ:
      nexp = 0;
      kind = bitwuzla::Kind::FP_GEQ;
      break;
    case Token::FP_GT:
      nexp = 0;
      kind = bitwuzla::Kind::FP_GT;
      break;
    case Token::FP_IS_INF:
      nexp = 1;
      kind = bitwuzla::Kind::FP_IS_INF;
      break;
    case Token::FP_IS_NAN:
      nexp = 1;
      kind = bitwuzla::Kind::FP_IS_NAN;
      break;
    case Token::FP_IS_NEG:
      nexp = 1;
      kind = bitwuzla::Kind::FP_IS_NEG;
      break;
    case Token::FP_IS_NORMAL:
      nexp = 1;
      kind = bitwuzla::Kind::FP_IS_NORMAL;
      break;
    case Token::FP_IS_POS:
      nexp = 1;
      kind = bitwuzla::Kind::FP_IS_POS;
      break;
    case Token::FP_IS_SUBNORMAL:
      nexp = 1;
      kind = bitwuzla::Kind::FP_IS_SUBNORMAL;
      break;
    case Token::FP_IS_ZERO:
      nexp = 1;
      kind = bitwuzla::Kind::FP_IS_ZERO;
      break;
    case Token::FP_LEQ:
      nexp = 0;
      kind = bitwuzla::Kind::FP_LEQ;
      break;
    case Token::FP_LT:
      nexp = 0;
      kind = bitwuzla::Kind::FP_LT;
      break;
    case Token::FP_MAX:
      nexp = 2;
      kind = bitwuzla::Kind::FP_MAX;
      break;
    case Token::FP_MIN:
      nexp = 2;
      kind = bitwuzla::Kind::FP_MIN;
      break;
    case Token::FP_MUL:
      nexp   = 3;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_MUL;
      break;
    case Token::FP_NEG:
      nexp = 1;
      kind = bitwuzla::Kind::FP_NEG;
      break;
    case Token::FP_REM:
      nexp = 2;
      kind = bitwuzla::Kind::FP_REM;
      break;
    case Token::FP_RTI:
      nexp   = 2;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_RTI;
      break;
    case Token::FP_SQRT:
      nexp   = 2;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_SQRT;
      break;
    case Token::FP_SUB:
      nexp   = 3;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_SUB;
      break;
    case Token::FP_TO_FP_UNSIGNED:
      nexp   = 2;
      nidxs  = 2;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_TO_FP_FROM_UBV;
      break;
    case Token::FP_TO_SBV:
      nexp   = 2;
      nidxs  = 2;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_TO_SBV;
      break;
    case Token::FP_TO_UBV:
      nexp   = 2;
      nidxs  = 2;
      has_rm = true;
      kind   = bitwuzla::Kind::FP_TO_UBV;
      break;
    default: assert(false);
  }
  if (!pop_args(item_open, nexp, args, nidxs, &idxs))
  {
    return false;
  }
  assert(args.size());

  if (token == Token::FP_FP)
  {
    if (!args[0].sort().is_bv() || args[0].sort().bv_size() != 1)
    {
      return error(
          "expected bit-vector term of size 1 at index 0 as argument to '"
              + std::to_string(token) + "'",
          &item_open.d_coo);
    }
    if (!args[1].sort().is_bv())
    {
      return error("expected bit-vector term at index 1 as argument to '"
                       + std::to_string(token) + "'",
                   &item_open.d_coo);
    }
    if (!args[2].sort().is_bv())
    {
      return error("expected bit-vector term at index 2 as argument to '"
                       + std::to_string(token) + "'",
                   &item_open.d_coo);
    }
    if (args[0].is_value() && args[1].is_value() && args[2].is_value())
    {
      d_work_args.push_back(bitwuzla::mk_fp_value(args[0], args[1], args[2]));
      return true;
    }
  }
  else
  {
    for (size_t i = 0, n = args.size(); i < n; ++i)
    {
      if (has_rm && i == 0)
      {
        return error("expected rounding-mode term at index 0 as argument to '"
                         + std::to_string(token) + "'",
                     &item_open.d_coo);
      }
      else
      {
        if (!args[i].sort().is_fp())
        {
          return error("expected floating-point term at index "
                           + std::to_string(i) + " as argument to '"
                           + std::to_string(token) + "'",
                       &item_open.d_coo);
        }
      }
      if ((!has_rm && i > 0) || (has_rm && i > 1))
      {
        if (args[i].sort() != args[i - 1].sort())
        {
          return error("expected terms of same sort at indices "
                           + std::to_string(i - 1) + " and " + std::to_string(i)
                           + " as argument to '" + std::to_string(token) + "'",
                       &item_open.d_coo);
        }
      }
    }
  }
  d_work_args.push_back(bitwuzla::mk_term(kind, args, idxs));
  return true;
}

bool
Parser::close_term_fun_app(const ParsedItem& item_open)
{
  assert(std::holds_alternative<SymbolTable::Node*>(item_open.d_parsed));
  SymbolTable::Node* node = std::get<SymbolTable::Node*>(item_open.d_parsed);
  bitwuzla::Term& fun     = node->d_term;
  assert(!fun.is_null());
  if (!fun.sort().is_fun())
  {
    return error("expected fun", &item_open.d_coo);
  }
  size_t arity = fun.sort().fun_arity();
  if (nargs() != arity)
  {
    return error("expected " + std::to_string(arity) + " arguments to '"
                     + std::to_string(item_open.d_token) + "', got '"
                     + std::to_string(nargs()) + "'",
                 &item_open.d_coo);
  }
  std::vector<bitwuzla::Term> args;
  if (!pop_args(item_open, arity, args))
  {
    return false;
  }
  const std::vector<bitwuzla::Sort>& domain = fun.sort().fun_domain();
  assert(args.size() == arity);
  assert(domain.size() == arity);
  for (size_t i = 0; i < arity; ++i)
  {
    if (domain[i] != args[i].sort())
    {
      return error("expected term of sort '" + domain[i].str() + "', got '"
                       + args[i].sort().str() + "'",
                   &item_open.d_coo);
    }
  }
  args.insert(args.begin(), fun);
  d_work_args.push_back(bitwuzla::mk_term(bitwuzla::Kind::APPLY, args));
  return true;
}

bool
Parser::close_term_let(const ParsedItem& item_open)
{
  if (nargs() == 0 || !peek_is_term_arg())
  {
    return error("expected (single) term as argument to '"
                     + std::to_string(item_open.d_token) + "'",
                 &item_open.d_coo);
  }
  bitwuzla::Term term = pop_term_arg();
  for (size_t i = 0, n = nargs(); i < n; ++i)
  {
    SymbolTable::Node* symbol = pop_node_arg();
    assert(symbol);
    assert(symbol->d_token == Token::SYMBOL);
    assert(symbol->d_coo.line);
    assert(!symbol->d_term.is_null());
    d_table.remove(symbol);
  }
  d_work_args.push_back(term);
  return true;
}

bool
Parser::close_term_letbind(const ParsedItem& item_open)
{
  if (nargs() != 2)
  {
    return error("expected 2 arguments to variable binding, got '"
                     + std::to_string(nargs()) + "'",
                 &item_open.d_coo);
  }
  if (!peek_is_term_arg())
  {
    return error("expected term", &item_open.d_coo);
  }
  bitwuzla::Term term       = pop_term_arg();
  SymbolTable::Node* symbol = peek_node_arg();
  assert(symbol->d_term.is_null());
  assert(!symbol->d_is_bound);
  symbol->d_term     = term;
  symbol->d_is_bound = true;
  d_is_var_binding   = true;
  return true;
}

bool
Parser::close_term_parletbind(const ParsedItem& item_open)
{
  (void) item_open;
  assert(d_is_var_binding);
  d_is_var_binding = false;
  assert(!d_expect_body);
  d_expect_body = true;
  return true;
}

bool
Parser::close_term_quant(const ParsedItem& item_open)
{
  assert(item_open.d_token == Token::FORALL
         || item_open.d_token == Token::EXISTS);
  if (!peek_is_term_arg() || !peek_term_arg().sort().is_bool())
  {
    return error("expected Boolean term as body to '"
                     + std::to_string(item_open.d_token) + "'",
                 &item_open.d_coo);
  }
  std::vector<bitwuzla::Term> args;
  pop_args(item_open, nargs(), args);
  for (size_t i = 0, n = nargs() - 1; i < n; ++i)
  {
    if (!args[i].is_variable())
    {
      return error("expected variable at index " + std::to_string(i)
                       + " as argument to '" + std::to_string(item_open.d_token)
                       + "'",
                   &item_open.d_coo);
    }
  }
  d_work_args.push_back(bitwuzla::mk_term(item_open.d_token == Token::FORALL
                                              ? bitwuzla::Kind::FORALL
                                              : bitwuzla::Kind::EXISTS,
                                          args));
  return true;
}

bool
Parser::close_term_sorted_var(const ParsedItem& item_open)
{
  if (nargs() != 1)
  {
    return error("expected one single variable at sorted variable expression",
                 &item_open.d_coo);
  }
  assert(peek_is_term_arg());
  assert(peek_term_arg().is_variable());
  assert(!d_is_sorted_var);
  d_is_sorted_var = true;
  return true;
}

bool
Parser::close_term_sorted_vars(const ParsedItem& item_open)
{
  (void) item_open;
  assert(d_is_sorted_var);
  d_is_sorted_var = false;
  assert(!d_expect_body);
  d_expect_body = true;
  return true;
}

/* -------------------------------------------------------------------------- */

bool
Parser::parse_sort(bool look_ahead, Token la)
{
  Token token = look_ahead ? la : next_token();
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
  assert(peek_is_uint64_arg());
  uint64_t res = std::get<uint64_t>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

bitwuzla::Sort
Parser::pop_sort_arg()
{
  assert(peek_is_sort_arg());
  bitwuzla::Sort res = std::get<bitwuzla::Sort>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

bitwuzla::Term
Parser::pop_term_arg()
{
  assert(peek_is_term_arg());
  bitwuzla::Term res = std::get<bitwuzla::Term>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

std::string
Parser::pop_str_arg()
{
  assert(peek_is_str_arg());
  std::string res = std::get<std::string>(d_work_args.back());
  d_work_args.pop_back();
  return res;
}

SymbolTable::Node*
Parser::pop_node_arg()
{
  assert(peek_is_node_arg());
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

const bitwuzla::Term&
Parser::peek_term_arg() const
{
  assert(std::holds_alternative<bitwuzla::Term>(d_work_args.back()));
  return std::get<bitwuzla::Term>(d_work_args.back());
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

bool
Parser::pop_args(const ParsedItem& item_open,
                 size_t nexp,
                 std::vector<bitwuzla::Term>& args,
                 size_t nidxs,
                 std::vector<uint64_t>* idxs)
{
  assert(nexp > 0 || nidxs == 0);
  if (nexp > 0 && nargs() != nexp)
  {
    return error("expected " + std::to_string(nexp) + " argument"
                     + (nexp > 1 ? "s" : "") + " to '"
                     + std::to_string(item_open.d_token) + "', got '"
                     + std::to_string(nargs()) + "'",
                 &item_open.d_coo);
  }
  nexp = nargs();
  assert(args.empty());
  args.reserve(nexp);
  for (size_t i = 0, n = nexp - nidxs; i < n; ++i)
  {
    size_t idx = n - i - 1;
    if (!peek_is_term_arg())
    {
      return error("expected term as argument at index " + std::to_string(idx)
                       + " to '" + std::to_string(item_open.d_token) + "'",
                   &item_open.d_coo);
    }
    args[idx] = pop_term_arg();
  }
  assert(!idxs || idxs->empty());
  if (idxs)
  {
    idxs->reserve(nidxs);
    for (size_t i = 0; i < nidxs; ++i)
    {
      size_t idx = nidxs - i - 1;
      if (!peek_is_uint64_arg())
      {
        return error("expected integer argument at index " + std::to_string(idx)
                         + " to '" + std::to_string(item_open.d_token) + "'",
                     &item_open.d_coo);
      }
      (*idxs)[idx] = pop_uint64_arg();
    }
  }
  return true;
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
