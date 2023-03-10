#include "parser/smt2/parser.h"

#include <algorithm>
#include <iostream>

#include "bitwuzla/cpp/bitwuzla.h"

namespace bzla {
namespace parser::smt2 {

/* Parser public ------------------------------------------------------------ */

Parser::Parser(bitwuzla::Options& options,
               std::istream* infile,
               const std::string& infile_name)
    : d_options(options),
      d_infile_name(infile_name),
      d_lexer(new Lexer(infile)),
      d_log_level(options.get(bitwuzla::Option::LOGLEVEL)),
      d_verbosity(options.get(bitwuzla::Option::VERBOSITY)),
      d_logger(d_log_level, d_verbosity)
{
  d_token_class_mask = static_cast<uint32_t>(TokenClass::COMMAND)
                       | static_cast<uint32_t>(TokenClass::CORE)
                       | static_cast<uint32_t>(TokenClass::KEYWORD)
                       | static_cast<uint32_t>(TokenClass::RESERVED);
  d_work_args_control.push_back(0);
}

std::string
Parser::parse()
{
  util::Timer timer(d_statistics.time_parse);

  while (parse_command() && !d_done && !terminate())
    ;

  if (d_error.empty())
  {
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
  }

  Msg(1) << "parsed " << d_statistics.num_commands << " commands in "
         << d_statistics.time_parse.elapsed() << " seconds";
  return d_error;
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
Parser::init_logic()
{
  if (d_logic.empty())
  {
    enable_theory("ALL");
  }
}

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
    token       = d_last_node->d_token;
  }
  return token;
}

bool
Parser::parse_command()
{
  Token token = next_token();

  if (token == Token::ENDOFFILE)
  {
    d_done = true;
    return true;
  }

  if (token == Token::INVALID)
  {
    return error_invalid();
  }

  if (token != Token::LPAR)
  {
    return error("missing '('");
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

  Msg(1) << "parse command '" << token << "'";

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
  init_logic();
  init_bitwuzla();
  Token la = next_token();
  if (!parse_term(true, la))
  {
    return false;
  }
  if (!peek_term_arg().sort().is_bool())
  {
    return error_arg("asserted term is not a formula");
  }
  bitwuzla::Term term = pop_term_arg();
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
  init_logic();
  init_bitwuzla();
  if (d_statistics.num_check_sat
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
    assumptions.resize(nargs());
    for (size_t i = 0, n = nargs(); i < n; ++i)
    {
      size_t idx = n - i - 1;
      if (!peek_term_arg().sort().is_bool())
      {
        return error_arg("assumption at index " + std::to_string(idx)
                         + " is not a formula");
      }
      assumptions[idx] = pop_term_arg();
    }
    if (!parse_rpars(1))
    {
      return false;
    }
    d_result = d_bitwuzla->check_sat(assumptions);
  }
  else
  {
    if (!parse_rpars(1))
    {
      return false;
    }
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
  return true;
}

bool
Parser::parse_command_declare_fun(bool is_const)
{
  init_logic();
  if (!parse_symbol(is_const ? "after 'declare-const'" : "after 'declare-fun'"))
  {
    return false;
  }
  assert(nargs() == 1);
  if (peek_node_arg()->d_coo.line)
  {
    return error_arg("symbol '" + peek_node_arg()->d_symbol
                     + "' already defined at line "
                     + std::to_string(peek_node_arg()->d_coo.line) + " column "
                     + std::to_string(peek_node_arg()->d_coo.col));
  }
  SymbolTable::Node* symbol = pop_node_arg(true);

  std::vector<bitwuzla::Sort> domain;
  if (!is_const)
  {
    if (!parse_lpars(1))
    {
      return false;
    }
    Token la;
    for (;;)
    {
      la = next_token();
      if (la == Token::RPAR)
      {
        break;
      }
      if (!parse_sort(true, la))
      {
        return false;
      }
    }
    size_t size_args = nargs();
    domain.resize(size_args);
    for (size_t i = 0, n = size_args; i < n; ++i)
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
  init_logic();
  if (!parse_symbol("after 'declare-sort'"))
  {
    return false;
  }
  assert(nargs() == 1);
  if (peek_node_arg()->d_coo.line)
  {
    return error_arg("symbol '" + peek_node_arg()->d_symbol
                     + "' alread defined at line "
                     + std::to_string(peek_node_arg()->d_coo.line) + " column "
                     + std::to_string(peek_node_arg()->d_coo.col));
  }
  SymbolTable::Node* symbol = pop_node_arg(true);
  if (!parse_uint64())
  {
    return false;
  }
  if (peek_uint64_arg() != 0)
  {
    return error_arg("'declare-sort' of arity > 0 not supported");
  }
  (void) pop_uint64_arg();
  symbol->d_sort = bitwuzla::mk_uninterpreted_sort(symbol->d_symbol);
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
  init_logic();
  if (!parse_symbol("after 'define-fun'"))
  {
    return false;
  }
  assert(nargs() == 1);
  if (peek_node_arg()->d_coo.line)
  {
    return error_arg("symbol '" + peek_node_arg()->d_symbol
                     + "' alread defined at line "
                     + std::to_string(peek_node_arg()->d_coo.line) + " column "
                     + std::to_string(peek_node_arg()->d_coo.col));
  }
  SymbolTable::Node* symbol = pop_node_arg(true);

  if (!parse_lpars(1))
  {
    return false;
  }

  std::vector<bitwuzla::Term> args;
  Token la;
  for (;;)
  {
    la = next_token();
    if (la == Token::RPAR)
    {
      break;
    }
    if (la != Token::LPAR)
    {
      return error("missing '('");
    }
    if (!parse_symbol("in sorted var", true))
    {
      return false;
    }
    SymbolTable::Node* symbol = peek_node_arg();
    if (!parse_sort())
    {
      return false;
    }
    parse_rpars(1);
    symbol->d_term = bitwuzla::mk_var(pop_sort_arg(), symbol->d_symbol);
    args.push_back(symbol->d_term);
  }

  if (!parse_sort())
  {
    return false;
  }
  bitwuzla::Sort sort = pop_sort_arg();

  if (!parse_term())
  {
    return false;
  }

  if (peek_term_arg().sort() != sort)
  {
    return error_arg("expected term of sort '" + sort.str() + "' but got '"
                     + peek_term_arg().sort().str());
  }
  bitwuzla::Term body = pop_term_arg();

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
  init_logic();
  if (!parse_symbol("after 'define-sort'"))
  {
    return false;
  }
  assert(nargs() == 1);
  if (peek_node_arg()->d_coo.line)
  {
    return error_arg("symbol '" + peek_node_arg()->d_symbol
                     + "' alread defined at line "
                     + std::to_string(peek_node_arg()->d_coo.line) + " column "
                     + std::to_string(peek_node_arg()->d_coo.col));
  }
  SymbolTable::Node* symbol = pop_node_arg(true);

  if (!parse_lpars(1))
  {
    return false;
  }
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }
  if (token != Token::RPAR)
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

  (*d_out) << echo << std::endl;
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
  init_logic();
  init_bitwuzla();
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
  init_logic();
  init_bitwuzla();
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
  init_logic();
  init_bitwuzla();
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
  init_logic();
  init_bitwuzla();
  if (!d_options.get(bitwuzla::Option::PRODUCE_MODELS))
  {
    return error("model generation is not enabled");
  }
  if (d_result != bitwuzla::Result::SAT)
  {
    return true;
  }
  if (!parse_lpars(1))
  {
    return false;
  }
  std::vector<std::string> repr;
  if (!parse_term_list(&repr))
  {
    return false;
  }
  if (!parse_rpars(1))
  {
    return false;
  }
  size_t size_args = nargs();
  std::vector<bitwuzla::Term> args(size_args);
  for (size_t i = 0; i < size_args; ++i)
  {
    size_t idx = size_args - i - 1;
    args[idx]  = pop_term_arg();
  }
  (*d_out) << "(";
  std::stringstream ss;
  if (size_args > 1)
  {
    (*d_out) << std::endl;
    ss << std::endl;
  }
  ss << " ";
  const std::string& pref = ss.str();
  for (size_t i = 0; i < size_args; ++i)
  {
    (*d_out) << "(";
    if (i > 0)
    {
      (*d_out) << pref;
    }
    (*d_out) << repr[i] << " " << d_bitwuzla->get_value(args[i]);
    (*d_out) << ")";
  }
  if (size_args > 1)
  {
    (*d_out) << std::endl;
  }
  (*d_out) << ")" << std::endl;
  ;
  d_out->flush();
  return true;
}

bool
Parser::parse_command_pop()
{
  init_logic();
  init_bitwuzla();

  if (!parse_uint64())
  {
    return false;
  }
  if (!parse_rpars(1))
  {
    return false;
  }
  if (peek_uint64_arg() > d_scope_level)
  {
    return error_arg("attempting to pop '" + std::to_string(peek_uint64_arg())
                     + "' but only '" + std::to_string(peek_uint64_arg())
                     + "' have been pushed previously");
  }
  uint64_t nlevels = pop_uint64_arg();

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
  init_logic();
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
  if (!is_token_class(token, TokenClass::KEYWORD) && token != Token::ATTRIBUTE)
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
      if (token == Token::RPAR)
      {
        return error("missing value for ':status'");
      }
      return error("invalid value '" + d_lexer->token() + "' for ':status'");
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
  if (!skip_sexprs(1))
  {
    return false;
  }
  print_success();
  return true;
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
    if (!check_token(token))
    {
      return false;
    }
    assert(d_lexer->has_token());
    assert(d_lexer->token()[0] == ':');
    std::string opt = d_lexer->token().substr(1);
    token           = next_token();
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
      uint64_t val = std::stoull(d_lexer->token());
      push_arg(val);
      return true;
    }
    catch (...)
    {
      return error("invalid 64 bit integer '" + d_lexer->token() + "'");
    }
  }
  return error("expected 64 bit integer");
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
    return error("expected symbol " + error_msg);
  }
  assert(d_last_node->d_token == Token::SYMBOL);
  // shadow previously defined symbols
  if (shadow && d_last_node->d_coo.line)
  {
    d_last_node        = d_table.insert(token, d_lexer->token(), d_scope_level);
    assert(d_last_node->has_symbol());
    d_last_node->d_coo = d_lexer->coo();
  }
  push_arg(d_last_node);
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
      if (!close_term())
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
Parser::parse_term_list(std::vector<std::string>* repr)
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
    if (repr && la == Token::SYMBOL)
    {
      assert(d_last_node->has_symbol());
      repr->push_back(d_last_node->d_is_piped
                          ? "|" + d_last_node->d_symbol + "|"
                          : d_last_node->d_symbol);
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
  assert(token != Token::RPAR);
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
      assert(peek_is_node_arg());
      peek_node_arg()->d_coo = d_lexer->coo();
    }
    else if (d_is_sorted_var)
    {
      // parse <sorted_var>: <symbol> <sort>
      d_work.emplace_back(Token::SORTED_VAR, d_lexer->coo());
      d_is_sorted_var           = false;
      if (!parse_symbol("in sorted var", true))
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
      symbol->d_term = bitwuzla::mk_var(sort, symbol->d_symbol);
      push_arg(symbol->d_term);
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
    if (token == Token::SYMBOL)
    {
      d_work.emplace_back(token, d_last_node, d_lexer->coo());
    }
    else
    {
      d_work.emplace_back(token, d_lexer->coo());
    }
    if (!parse_open_term_symbol())
    {
      return false;
    }
  }
  else if (token == Token::NAMED)
  {
    push_arg(d_last_node);
    if (!parse_symbol("in sorted var", true))
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
    push_arg(bitwuzla::mk_bv_value(sort, val));
  }
  else if (token == Token::HEXADECIMAL_VALUE)
  {
    assert(d_lexer->has_token());
    std::string val     = d_lexer->token().substr(2);
    bitwuzla::Sort sort = bitwuzla::mk_bv_sort(val.size() * 4);
    push_arg(bitwuzla::mk_bv_value(sort, val, 16));
  }
  else if (token == Token::DECIMAL_VALUE || token == Token::REAL_VALUE)
  {
    assert(d_lexer->has_token());
    push_arg(d_lexer->token());
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
    if (d_work.size() < 2 || d_work[d_work.size() - 2].d_token != Token::LPAR)
    {
      return error("missing '(' before '(as'", d_work.back().d_coo);
    }
    close_term_scope();
    return true;
  }
  return error("invalid identifier '" + iden + "'");
}

bool
Parser::parse_open_term_indexed()
{
  Lexer::Coordinate coo = d_lexer->last_coo();

  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }

  Token token_kind        = token;
  bitwuzla::Kind kind     = bitwuzla::Kind::VALUE;
  SymbolTable::Node* node = d_last_node;

  uint64_t min    = 0;
  uint64_t nidxs  = 1;

  if (token == Token::SYMBOL)
  {
    token_kind = Token::BV_VALUE;
  }

  switch (token)
  {
    case Token::BV_REPEAT: kind = bitwuzla::Kind::BV_REPEAT; break;

    case Token::BV_ROTATE_LEFT: kind = bitwuzla::Kind::BV_ROLI; break;

    case Token::BV_ROTATE_RIGHT: kind = bitwuzla::Kind::BV_RORI; break;

    case Token::BV_SIGN_EXTEND: kind = bitwuzla::Kind::BV_SIGN_EXTEND; break;

    case Token::BV_ZERO_EXTEND: kind = bitwuzla::Kind::BV_ZERO_EXTEND; break;

    case Token::BV_EXTRACT:
      kind  = bitwuzla::Kind::BV_EXTRACT;
      nidxs = 2;
      break;

    case Token::FP_TO_FP:
    case Token::FP_TO_FP_UNSIGNED:
      // only used to mark as non-value, ignored
      kind = bitwuzla::Kind::FP_TO_FP_FROM_UBV;
      [[fallthrough]];
    case Token::FP_NAN:
    case Token::FP_NEG_INF:
    case Token::FP_NEG_ZERO:
    case Token::FP_POS_INF:
    case Token::FP_POS_ZERO:
      nidxs = 2;
      min   = 2;
      break;

    case Token::FP_TO_SBV:
      kind = bitwuzla::Kind::FP_TO_SBV;
      min  = 1;
      break;

    case Token::FP_TO_UBV:
      kind = bitwuzla::Kind::FP_TO_UBV;
      min  = 1;
      break;

    case Token::SYMBOL: {
      assert(d_lexer->has_token());
      min                    = 1;
      const std::string& val = d_lexer->token();
      if (val[0] != 'b' && val[1] != 'v')
      {
        return error("invalid indexed term '" + val + "'");
      }
      std::string v = val.substr(2);
      if (!std::all_of(
              v.begin(), v.end(), [](char c) { return std::isdigit(c); }))
      {
        return error("invalid bit-vector value '" + val + "'");
      }
      push_arg(v);
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
    if (min > peek_uint64_arg())
    {
      if (peek_uint64_arg() == 0)
      {
        return error_arg("expected non-zero index");
      }
      return error_arg("expected index > " + std::to_string(min - 1) + ", got '"
                       + std::to_string(peek_uint64_arg()) + "'");
    }
  }

  if (!parse_rpars(1))
  {
    return false;
  }

  if (kind == bitwuzla::Kind::VALUE)
  {
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
          push_arg(bitwuzla::mk_fp_nan(sort), &coo);
        }
        else if (token_kind == Token::FP_NEG_INF)
        {
          push_arg(bitwuzla::mk_fp_neg_inf(sort), &coo);
        }
        else if (token_kind == Token::FP_POS_INF)
        {
          push_arg(bitwuzla::mk_fp_pos_inf(sort), &coo);
        }
        else if (token_kind == Token::FP_NEG_ZERO)
        {
          push_arg(bitwuzla::mk_fp_neg_zero(sort), &coo);
        }
        else if (token_kind == Token::FP_POS_ZERO)
        {
          push_arg(bitwuzla::mk_fp_pos_zero(sort), &coo);
        }
      }
      break;

      default: {
        assert(token_kind == Token::BV_VALUE);
        assert(nargs() == 2);
        uint64_t size       = pop_uint64_arg();
        std::string val     = pop_str_arg();
        bitwuzla::Sort sort = bitwuzla::mk_bv_sort(size);
        push_arg(bitwuzla::mk_bv_value(sort, val, 10), &coo);
      }
    }
    close_term_scope();
  }
  else
  {
    // ((_ <indexed_op> <idxs) <terms>) -> (<indexed_op> <idxs> <terms>)
    if (d_work.size() < 2 || d_work[d_work.size() - 2].d_token != Token::LPAR)
    {
      return error("missing '(' before '(_'", d_work.back().d_coo);
    }
    assert(node);
    assert(token_kind != Token::SYMBOL);
    close_term_scope();
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
  ParsedItem& cur = d_work.back();
  Token token     = cur.d_token;

  if (is_token_class(token, TokenClass::COMMAND))
  {
    return error("unexpected command '" + std::to_string(token) + "'");
  }
  if (is_token_class(token, TokenClass::KEYWORD))
  {
    return error("unexpected keyword '" + std::to_string(token) + "'");
  }

  if (is_token_class(token, TokenClass::RESERVED))
  {
    if (token == Token::LET)
    {
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
      if (!parse_open_term_quant())
      {
        return false;
      }
    }
    else if (token == Token::UNDERSCORE)
    {
      d_work.pop_back();
      if (d_work.back().d_token != Token::LPAR)
      {
        return error("missing '(' before '_'");
      }
      if (!parse_open_term_indexed())
      {
        return false;
      }
    }
    else if (token == Token::AS)
    {
      if (!parse_open_term_as())
      {
        return false;
      }
    }
    else if (token == Token::BANG)
    {
      if (d_work.back().d_token != Token::LPAR)
      {
        return error("missing '(' before '" + std::to_string(token) + "'");
      }
      d_work.emplace_back(token, d_lexer->coo());
    }
    else
    {
      return error("unsupported reserved word '" + std::to_string(token) + "'");
    }
  }
  else if (token == Token::SYMBOL)
  {
    SymbolTable::Node* node = std::get<SymbolTable::Node*>(cur.d_parsed);
    if (node->d_term.is_null())
    {
      assert(node->has_symbol());
      return error("undefined symbol '" + node->d_symbol + "'");
    }
    d_work.pop_back();
    assert(!node->d_term.is_null());
    if (!node->d_term.sort().is_fun())
    {
      if (d_work.back().d_token == Token::LPAR)
      {
        return error("unexpected function application, '" + node->d_symbol
                     + "' is not a function");
      }
    }
    else
    {
      d_work.emplace_back(Token::FUN_APP, d_lexer->coo());
    }
    push_arg(node->d_term);
  }
  else if (token == Token::TRUE)
  {
    d_work.pop_back();
    push_arg(bitwuzla::mk_true());
  }
  else if (token == Token::FALSE)
  {
    d_work.pop_back();
    push_arg(bitwuzla::mk_false());
  }
  else if (token == Token::ATTRIBUTE)
  {
    assert(d_lexer->has_token());
    return error("unexpected attribute '" + d_lexer->token() + "'");
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
  else if (d_fp_enabled)
  {
    if (token == Token::REAL_DIV
        && (d_work.size() < 3
            || d_work[d_work.size() - 3].d_token != Token::FP_TO_FP))
    {
      return error("invalid term, '" + std::to_string(token)
                   + "' only allowed to represent rational values under '"
                   + std::to_string(Token::FP_TO_FP) + "'");
    }
    if (is_token_class(token, TokenClass::FP))
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
        push_arg(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNA));
      }
      else if (token == Token::FP_RM_RNE_LONG || token == Token::FP_RM_RNE)
      {
        d_work.pop_back();
        push_arg(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNE));
      }
      else if (token == Token::FP_RM_RTN_LONG || token == Token::FP_RM_RTN)
      {
        d_work.pop_back();
        push_arg(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTN));
      }
      else if (token == Token::FP_RM_RTP_LONG || token == Token::FP_RM_RTP)
      {
        d_work.pop_back();
        push_arg(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTP));
      }
      else if (token == Token::FP_RM_RTZ_LONG || token == Token::FP_RM_RTZ)
      {
        d_work.pop_back();
        push_arg(bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTZ));
      }
    }
  }
  else if (token != Token::REAL_DIV)
  {
    return error("unexpected token '" + std::to_string(token) + "'");
  }
  return true;
}

bool
Parser::close_term()
{
  uint64_t nopen = d_term_open;
  if (!nopen)
  {
    return error("expected expression");
  }

  assert(d_work.size());
  const ParsedItem& item = d_work.back();
  if (item.d_token == Token::LPAR)
  {
    if (nargs() == 0)
    {
      return error("unexpected '()'", item.d_coo);
    }
    return error("missing identifier, invalid term", item.d_coo);
  }
  d_work.pop_back();

  if (d_expect_body)
  {
    return error("missing body to '" + std::to_string(item.d_token));
  }

  bool res = false;
  switch (item.d_token)
  {
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

    case Token::BV_VALUE:
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

    case Token::FUN_APP: res = close_term_fun_app(item); break;

    case Token::LET: res = close_term_let(item); break;

    case Token::LETBIND: res = close_term_letbind(item); break;

    case Token::PARLETBIND: res = close_term_parletbind(item); break;

    case Token::SORTED_VAR: res = close_term_sorted_var(item); break;

    case Token::SORTED_VARS: res = close_term_sorted_vars(item); break;

    default:
      return error("unsupported term kind '" + std::to_string(item.d_token)
                   + "'");
  }
  if (d_work.size() == 0 || d_work.back().d_token != Token::LPAR)
  {
    return error("missing '(' before '" + std::to_string(item.d_token) + "'",
                 item.d_coo);
  }
  close_term_scope();
  return res;
}

bool
Parser::close_term_as(const ParsedItem& item_open)
{
  if (nargs() != 2)
  {
    return error("expected exactly 1 term argument to 'as', got "
                     + std::to_string(nargs() > 0 ? nargs() - 1 : 0),
                 item_open.d_coo);
  }
  bitwuzla::Term term = pop_term_arg();
  bitwuzla::Sort sort = pop_sort_arg();
  assert(sort.is_array());
  push_arg(bitwuzla::mk_const_array(sort, term), &item_open.d_coo);
  return true;
}

bool
Parser::close_term_bang(const ParsedItem& item_open)
{
  if (nargs() != 3)
  {
    return error("invalid annotation syntax, expected 3 arguments, got "
                     + std::to_string(nargs()),
                 item_open.d_coo);
  }
  if (!peek_is_node_arg())
  {
    return error(
        "invalid annotation syntax, expected symbol as third argument");
  }
  if (!peek_is_node_arg())
  {
    return error_arg(
        "invalid annotation syntax, expected ':named' as second argument");
  }
  SymbolTable::Node* symbol = pop_node_arg();
  if (peek_node_arg()->d_token != Token::NAMED)
  {
    return error_arg(
        "invalid annotation syntax, expected ':named' as second argument");
  }
  (void) pop_node_arg();
  if (!peek_is_term_arg())
  {
    return error_arg(
        "invalid annotation syntax, expected term as first argument");
  }
  symbol->d_term = pop_term_arg();
  push_arg(symbol->d_term, &item_open.d_coo);
  return true;
}

bool
Parser::close_term_array(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  std::vector<bitwuzla::Term> args;
  if (token == Token::ARRAY_SELECT)
  {
    if (!pop_args(item_open, args))
    {
      return false;
    }
    push_arg(
        bitwuzla::mk_term(bitwuzla::Kind::ARRAY_SELECT, {args[0], args[1]}),
        &item_open.d_coo);
    return true;
  }

  assert(item_open.d_token == Token::ARRAY_STORE);
  if (!pop_args(item_open, args))
  {
    return false;
  }
  push_arg(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE, args),
           &item_open.d_coo);
  return true;
}

bool
Parser::close_term_core(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  std::vector<bitwuzla::Term> args;
  bitwuzla::Kind kind;

  switch (token)
  {
    case Token::AND: kind = bitwuzla::Kind::AND; break;
    case Token::DISTINCT: kind = bitwuzla::Kind::DISTINCT; break;
    case Token::EQUAL: kind = bitwuzla::Kind::EQUAL; break;
    case Token::IMPLIES: kind = bitwuzla::Kind::IMPLIES; break;
    case Token::ITE: kind = bitwuzla::Kind::ITE; break;
    case Token::NOT: kind = bitwuzla::Kind::NOT; break;
    case Token::OR: kind = bitwuzla::Kind::OR; break;
    case Token::XOR: kind = bitwuzla::Kind::XOR; break;
    default: assert(false);
  }
  if (!pop_args(item_open, args))
  {
    return false;
  }
  push_arg(bitwuzla::mk_term(kind, args), &item_open.d_coo);
  return true;
}

bool
Parser::close_term_bv(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> idxs;
  bitwuzla::Kind kind;

  if (token == Token::BV_VALUE)
  {
    assert(nargs() == 2);
    uint64_t size   = pop_uint64_arg();
    std::string val = pop_str_arg();
    push_arg(bitwuzla::mk_bv_value(bitwuzla::mk_bv_sort(size), val, 10),
             &item_open.d_coo);
    return true;
  }

  switch (token)
  {
    case Token::BV_ADD: kind = bitwuzla::Kind::BV_ADD; break;
    case Token::BV_AND: kind = bitwuzla::Kind::BV_AND; break;
    case Token::BV_ASHR: kind = bitwuzla::Kind::BV_ASHR; break;
    case Token::BV_COMP: kind = bitwuzla::Kind::BV_COMP; break;
    case Token::BV_CONCAT: kind = bitwuzla::Kind::BV_CONCAT; break;
    case Token::BV_EXTRACT: kind = bitwuzla::Kind::BV_EXTRACT; break;
    case Token::BV_LSHR: kind = bitwuzla::Kind::BV_SHR; break;
    case Token::BV_MUL: kind = bitwuzla::Kind::BV_MUL; break;
    case Token::BV_NAND: kind = bitwuzla::Kind::BV_NAND; break;
    case Token::BV_NEG: kind = bitwuzla::Kind::BV_NEG; break;
    case Token::BV_NOR: kind = bitwuzla::Kind::BV_NOR; break;
    case Token::BV_NOT: kind = bitwuzla::Kind::BV_NOT; break;
    case Token::BV_OR: kind = bitwuzla::Kind::BV_OR; break;
    case Token::BV_REPEAT: kind = bitwuzla::Kind::BV_REPEAT; break;
    case Token::BV_ROTATE_LEFT: kind = bitwuzla::Kind::BV_ROLI; break;
    case Token::BV_ROTATE_RIGHT: kind = bitwuzla::Kind::BV_RORI; break;
    case Token::BV_SDIV: kind = bitwuzla::Kind::BV_SDIV; break;
    case Token::BV_SGE: kind = bitwuzla::Kind::BV_SGE; break;
    case Token::BV_SGT: kind = bitwuzla::Kind::BV_SGT; break;
    case Token::BV_SHL: kind = bitwuzla::Kind::BV_SHL; break;
    case Token::BV_SIGN_EXTEND: kind = bitwuzla::Kind::BV_SIGN_EXTEND; break;
    case Token::BV_SLE: kind = bitwuzla::Kind::BV_SLE; break;
    case Token::BV_SLT: kind = bitwuzla::Kind::BV_SLT; break;
    case Token::BV_SMOD: kind = bitwuzla::Kind::BV_SMOD; break;
    case Token::BV_SREM: kind = bitwuzla::Kind::BV_SREM; break;
    case Token::BV_SUB: kind = bitwuzla::Kind::BV_SUB; break;
    case Token::BV_UDIV: kind = bitwuzla::Kind::BV_UDIV; break;
    case Token::BV_UGE: kind = bitwuzla::Kind::BV_UGE; break;
    case Token::BV_UGT: kind = bitwuzla::Kind::BV_UGT; break;
    case Token::BV_ULE: kind = bitwuzla::Kind::BV_ULE; break;
    case Token::BV_ULT: kind = bitwuzla::Kind::BV_ULT; break;
    case Token::BV_UREM: kind = bitwuzla::Kind::BV_UREM; break;
    case Token::BV_XNOR: kind = bitwuzla::Kind::BV_XNOR; break;
    case Token::BV_XOR: kind = bitwuzla::Kind::BV_XOR; break;
    case Token::BV_ZERO_EXTEND: kind = bitwuzla::Kind::BV_ZERO_EXTEND; break;
    case Token::BV_REDOR: kind = bitwuzla::Kind::BV_REDOR; break;
    case Token::BV_REDAND: kind = bitwuzla::Kind::BV_REDAND; break;
    case Token::BV_REDXOR: kind = bitwuzla::Kind::BV_REDXOR; break;
    case Token::BV_SADDO: kind = bitwuzla::Kind::BV_SADD_OVERFLOW; break;
    case Token::BV_UADDO: kind = bitwuzla::Kind::BV_UADD_OVERFLOW; break;
    case Token::BV_SDIVO: kind = bitwuzla::Kind::BV_SDIV_OVERFLOW; break;
    case Token::BV_SMULO: kind = bitwuzla::Kind::BV_SMUL_OVERFLOW; break;
    case Token::BV_UMULO: kind = bitwuzla::Kind::BV_UMUL_OVERFLOW; break;
    case Token::BV_SSUBO: kind = bitwuzla::Kind::BV_SSUB_OVERFLOW; break;
    case Token::BV_USUBO: kind = bitwuzla::Kind::BV_USUB_OVERFLOW; break;
    default: assert(false);
  }
  if (!pop_args(item_open, args, &idxs))
  {
    return false;
  }
  assert(args.size());
  bitwuzla::Term res = bitwuzla::mk_term(kind, args, idxs);
  push_arg(res, &item_open.d_coo);
  return true;
}

bool
Parser::close_term_fp(const ParsedItem& item_open)
{
  Token token = item_open.d_token;
  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> idxs;
  std::vector<std::string> strs;
  bitwuzla::Kind kind;

  if (token == Token::FP_TO_FP || token == Token::FP_TO_FP_UNSIGNED)
  {
    if (!pop_args(item_open, args, &idxs, &strs))
    {
      return false;
    }
    if (!strs.empty())
    {
      assert(args.size() == 1);
      if (strs.size() == 1)
      {
        push_arg(bitwuzla::mk_fp_value(
                     bitwuzla::mk_fp_sort(idxs[0], idxs[1]), args[0], strs[0]),
                 &item_open.d_coo);
      }
      else
      {
        assert(strs.size() == 2);
        push_arg(bitwuzla::mk_fp_value(bitwuzla::mk_fp_sort(idxs[0], idxs[1]),
                                       args[0],
                                       strs[0],
                                       strs[1]),
                 &item_open.d_coo);
      }
    }
    if (args.size() == 1)
    {
      assert(idxs.size() == 2);
      assert(strs.empty());
      push_arg(bitwuzla::mk_term(bitwuzla::Kind::FP_TO_FP_FROM_BV, args, idxs),
               &item_open.d_coo);
      return true;
    }
    assert(args.size() == 2);
    push_arg(bitwuzla::mk_term(args[1].sort().is_bv()
                                   ? (token == Token::FP_TO_FP_UNSIGNED
                                          ? bitwuzla::Kind::FP_TO_FP_FROM_UBV
                                          : bitwuzla::Kind::FP_TO_FP_FROM_SBV)
                                   : bitwuzla::Kind::FP_TO_FP_FROM_FP,
                               {args[0], args[1]},
                               idxs),
             &item_open.d_coo);
    return true;
  }

  if (token == Token::REAL_DIV)
  {
    if (nargs() != 2)
    {
      return error("expected 2 arguments to '"
                       + std::to_string(item_open.d_token) + "', got "
                       + std::to_string(nargs()),
                   item_open.d_coo);
    }
    if (!peek_is_str_arg())
    {
      return error(
          "expected string representation of denominator as argument to '"
              + std::to_string(item_open.d_token) + "'",
          item_open.d_coo);
    }
    if (!peek_is_str_arg(d_work_args.size() - 2))
    {
      return error(
          "expected string representation of denominator as argument to '"
              + std::to_string(item_open.d_token) + "'",
          item_open.d_coo);
    }
    // nothing to do, we leave the strings on the args stack and only close
    // the current term
    return true;
  }

  switch (token)
  {
    case Token::FP_ABS: kind = bitwuzla::Kind::FP_ABS; break;
    case Token::FP_ADD: kind = bitwuzla::Kind::FP_ADD; break;
    case Token::FP_DIV: kind = bitwuzla::Kind::FP_DIV; break;
    case Token::FP_EQ: kind = bitwuzla::Kind::FP_EQUAL; break;
    case Token::FP_FMA: kind = bitwuzla::Kind::FP_FMA; break;
    case Token::FP_FP: kind = bitwuzla::Kind::FP_FP; break;
    case Token::FP_GEQ: kind = bitwuzla::Kind::FP_GEQ; break;
    case Token::FP_GT: kind = bitwuzla::Kind::FP_GT; break;
    case Token::FP_IS_INF: kind = bitwuzla::Kind::FP_IS_INF; break;
    case Token::FP_IS_NAN: kind = bitwuzla::Kind::FP_IS_NAN; break;
    case Token::FP_IS_NEG: kind = bitwuzla::Kind::FP_IS_NEG; break;
    case Token::FP_IS_NORMAL: kind = bitwuzla::Kind::FP_IS_NORMAL; break;
    case Token::FP_IS_POS: kind = bitwuzla::Kind::FP_IS_POS; break;
    case Token::FP_IS_SUBNORMAL: kind = bitwuzla::Kind::FP_IS_SUBNORMAL; break;
    case Token::FP_IS_ZERO: kind = bitwuzla::Kind::FP_IS_ZERO; break;
    case Token::FP_LEQ: kind = bitwuzla::Kind::FP_LEQ; break;
    case Token::FP_LT: kind = bitwuzla::Kind::FP_LT; break;
    case Token::FP_MAX: kind = bitwuzla::Kind::FP_MAX; break;
    case Token::FP_MIN: kind = bitwuzla::Kind::FP_MIN; break;
    case Token::FP_MUL: kind = bitwuzla::Kind::FP_MUL; break;
    case Token::FP_NEG: kind = bitwuzla::Kind::FP_NEG; break;
    case Token::FP_REM: kind = bitwuzla::Kind::FP_REM; break;
    case Token::FP_RTI: kind = bitwuzla::Kind::FP_RTI; break;
    case Token::FP_SQRT: kind = bitwuzla::Kind::FP_SQRT; break;
    case Token::FP_SUB: kind = bitwuzla::Kind::FP_SUB; break;
    case Token::FP_TO_SBV: kind = bitwuzla::Kind::FP_TO_SBV; break;
    case Token::FP_TO_UBV: kind = bitwuzla::Kind::FP_TO_UBV; break;
    default: assert(false);
  }
  if (!pop_args(item_open, args, &idxs))
  {
    return false;
  }
  assert(args.size());
  if (token == Token::FP_FP && args[0].is_value() && args[1].is_value()
      && args[2].is_value())
  {
    push_arg(bitwuzla::mk_fp_value(args[0], args[1], args[2]),
             &item_open.d_coo);
    return true;
  }
  push_arg(bitwuzla::mk_term(kind, args, idxs), &item_open.d_coo);
  return true;
}

bool
Parser::close_term_fun_app(const ParsedItem& item_open)
{
  assert(nargs() > 0);

  std::vector<bitwuzla::Term> args;
  if (!pop_args(item_open, args))
  {
    return false;
  }
  push_arg(bitwuzla::mk_term(bitwuzla::Kind::APPLY, args), &item_open.d_coo);
  return true;
}

bool
Parser::close_term_let(const ParsedItem& item_open)
{
  if (nargs() == 0 || !peek_is_term_arg())
  {
    return error_arg("expected (single) term as argument to '"
                     + std::to_string(item_open.d_token) + "'");
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
  push_arg(term, &item_open.d_coo);
  return true;
}

bool
Parser::close_term_letbind(const ParsedItem& item_open)
{
  if (nargs() != 2)
  {
    return error("expected 2 arguments to variable binding, got "
                     + std::to_string(nargs()),
                 item_open.d_coo);
  }
  if (!peek_is_term_arg())
  {
    return error_arg("expected term");
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
  std::vector<bitwuzla::Term> args;
  pop_args(item_open, args);
  push_arg(bitwuzla::mk_term(item_open.d_token == Token::FORALL
                                 ? bitwuzla::Kind::FORALL
                                 : bitwuzla::Kind::EXISTS,
                             args),
           &item_open.d_coo);
  return true;
}

bool
Parser::close_term_sorted_var(const ParsedItem& item_open)
{
  if (nargs() != 1)
  {
    return error("expected one single variable at sorted variable expression",
                 item_open.d_coo);
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
    push_arg(bitwuzla::mk_bool_sort());
    return true;
  }
  if (token == Token::FP_FLOAT16)
  {
    push_arg(bitwuzla::mk_fp_sort(5, 11));
    return true;
  }
  if (token == Token::FP_FLOAT32)
  {
    push_arg(bitwuzla::mk_fp_sort(8, 24));
    return true;
  }
  if (token == Token::FP_FLOAT64)
  {
    push_arg(bitwuzla::mk_fp_sort(11, 53));
    return true;
  }
  if (token == Token::FP_FLOAT128)
  {
    push_arg(bitwuzla::mk_fp_sort(15, 113));
    return true;
  }
  if (token == Token::FP_ROUNDINGMODE)
  {
    push_arg(bitwuzla::mk_rm_sort());
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
      if (d_arrays_enabled)
      {
        return error("expected '_' or 'Array'");
      }
      if (d_lexer->token() == std::to_string(Token::ARRAY))
      {
        return error("expected '_' (arrays not enabled)");
      }
      return error("expected '_'");
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
    push_arg(sort->d_sort, &sort->d_coo);
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
  Lexer::Coordinate coo = d_lexer->coo();
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
  push_arg(bitwuzla::mk_array_sort(index, element), &coo);
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

  Lexer::Coordinate coo = d_lexer->coo();
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
    push_arg(bitwuzla::mk_bv_sort(size), &coo);
    return true;
  }
  if (token == Token::FP_FLOATINGPOINT)
  {
    if (!parse_uint64())
    {
      return false;
    }
    uint64_t esize = pop_uint64_arg();
    if (esize < 2)
    {
      return error("invalid exponent size '" + std::to_string(esize)
                   + "', must be > 1");
    }
    if (!parse_uint64())
    {
      return false;
    }
    uint64_t ssize = pop_uint64_arg();
    if (ssize < 2)
    {
      return error("invalid significand size '" + std::to_string(ssize)
                   + "', must be > 1");
    }
    if (!parse_rpars(1))
    {
      return false;
    }
    push_arg(bitwuzla::mk_fp_sort(esize, ssize), &coo);
    return true;
  }
  return error("expected '" + std::to_string(Token::BV_BITVEC) + "' or '"
               + std::to_string(Token::FP_FLOATINGPOINT) + "'");
}

/* -------------------------------------------------------------------------- */

void
Parser::open_term_scope()
{
  d_work.emplace_back(Token::LPAR, d_lexer->coo());
  d_work_args_control.push_back(d_work_args.size());
  d_term_open += 1;
}

void
Parser::close_term_scope()
{
  assert(d_work.back().d_token == Token::LPAR);
  d_work.pop_back();
  d_work_args_control.pop_back();
  d_term_open -= 1;
}

/* -------------------------------------------------------------------------- */

bool
Parser::skip_sexprs(uint64_t nopen)
{
  while (nopen > 0)
  {
    Token token = next_token();
    if (token == Token::ENDOFFILE)
    {
      return error("missing ')' at end of file");
    }
    if (token == Token::INVALID)
    {
      return error_invalid();
    }
    if (token == Token::LPAR)
    {
      nopen += 1;
    }
    else if (token == Token::RPAR)
    {
      nopen -= 1;
    }
  }
  return 1;
}

/* -------------------------------------------------------------------------- */

bool
Parser::error(const std::string& error_msg, const Lexer::Coordinate& coo)
{
  assert(d_lexer);
  const Lexer::Coordinate* c = !coo.line ? &d_lexer->coo() : &coo;
  d_error = d_infile_name + ":" + std::to_string(c->line) + ":"
            + std::to_string(c->col) + ": " + error_msg;
  //#ifndef NDEBUG
  //  std::cout << "[error] " << d_error << std::endl;
  //  assert(false);
  //#endif
  return false;
}

bool
Parser::error_arg(const std::string& error_msg)
{
  assert(!d_work_args_coo.empty());
  return error(error_msg, d_work_args_coo.back());
}

bool
Parser::error_invalid()
{
  assert(d_lexer);
  assert(d_lexer->error());
  return error(d_lexer->error_msg());
}

bool
Parser::error_eof()
{
  return error("unexpected end of file", d_lexer->coo());
}

bool
Parser::check_token(Token token)
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
    return size_prefix;
  }

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

  if (size < 2)
  {
    return false;
  }

  if (logic == "ALL")
  {
    enable_theory("ALL");
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

const Lexer::Coordinate&
Parser::arg_coo(size_t idx) const
{
  assert(idx < d_work_args_coo.size());
  return d_work_args_coo[idx];
}

uint64_t
Parser::pop_uint64_arg()
{
  assert(peek_is_uint64_arg());
  uint64_t res = std::get<uint64_t>(d_work_args.back());
  d_work_args.pop_back();
  d_work_args_coo.pop_back();
  return res;
}

bitwuzla::Sort
Parser::pop_sort_arg()
{
  assert(peek_is_sort_arg());
  bitwuzla::Sort res = std::get<bitwuzla::Sort>(d_work_args.back());
  d_work_args.pop_back();
  d_work_args_coo.pop_back();
  return res;
}

bitwuzla::Term
Parser::pop_term_arg()
{
  assert(peek_is_term_arg());
  bitwuzla::Term res = std::get<bitwuzla::Term>(d_work_args.back());
  d_work_args.pop_back();
  d_work_args_coo.pop_back();
  return res;
}

std::string
Parser::pop_str_arg()
{
  assert(peek_is_str_arg());
  std::string res = std::get<std::string>(d_work_args.back());
  d_work_args.pop_back();
  d_work_args_coo.pop_back();
  return res;
}

SymbolTable::Node*
Parser::pop_node_arg(bool set_coo)
{
  assert(peek_is_node_arg());
  SymbolTable::Node* res = std::get<SymbolTable::Node*>(d_work_args.back());
  if (set_coo)
  {
    res->d_coo = d_work_args_coo.back();
  }
  d_work_args.pop_back();
  d_work_args_coo.pop_back();
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

uint64_t
Parser::peek_uint64_arg(size_t idx) const
{
  assert(idx < d_work_args.size());
  return std::get<uint64_t>(d_work_args[idx]);
}

const bitwuzla::Sort&
Parser::peek_sort_arg(size_t idx) const
{
  assert(idx < d_work_args.size());
  assert(std::holds_alternative<bitwuzla::Sort>(d_work_args[idx]));
  return std::get<bitwuzla::Sort>(d_work_args[idx]);
}

const bitwuzla::Term&
Parser::peek_term_arg(size_t idx) const
{
  assert(idx < d_work_args.size());
  assert(std::holds_alternative<bitwuzla::Term>(d_work_args[idx]));
  return std::get<bitwuzla::Term>(d_work_args[idx]);
}

const std::string&
Parser::peek_str_arg(size_t idx) const
{
  assert(idx < d_work_args.size());
  assert(std::holds_alternative<std::string>(d_work_args[idx]));
  return std::get<std::string>(d_work_args[idx]);
}

SymbolTable::Node*
Parser::peek_node_arg(size_t idx) const
{
  assert(idx < d_work_args.size());
  assert(std::holds_alternative<SymbolTable::Node*>(d_work_args[idx]));
  return std::get<SymbolTable::Node*>(d_work_args[idx]);
}

bool
Parser::peek_is_uint64_arg() const
{
  return std::holds_alternative<uint64_t>(d_work_args.back());
}

bool
Parser::peek_is_uint64_arg(size_t idx) const
{
  if (idx >= d_work_args.size())
  {
    return false;
  }
  return std::holds_alternative<uint64_t>(d_work_args[idx]);
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
Parser::peek_is_term_arg(size_t idx) const
{
  if (idx >= d_work_args.size())
  {
    return false;
  }
  return std::holds_alternative<bitwuzla::Term>(d_work_args[idx]);
}

bool
Parser::peek_is_str_arg() const
{
  return std::holds_alternative<std::string>(d_work_args.back());
}

bool
Parser::peek_is_str_arg(size_t idx) const
{
  if (idx >= d_work_args.size())
  {
    return false;
  }
  return std::holds_alternative<std::string>(d_work_args[idx]);
}

bool
Parser::peek_is_node_arg() const
{
  return std::holds_alternative<SymbolTable::Node*>(d_work_args.back());
}

bool
Parser::pop_args(const ParsedItem& item_open,
                 std::vector<bitwuzla::Term>& args,
                 std::vector<uint64_t>* idxs,
                 std::vector<std::string>* strs)
{
  Token token     = item_open.d_token;
  bool has_rm     = false;
  size_t n_args   = 0;
  size_t n_idxs   = 0;

  switch (token)
  {
    case Token::AND:
    case Token::DISTINCT:
    case Token::EQUAL:
    case Token::IMPLIES:
    case Token::OR:
    case Token::XOR:
    case Token::BV_ADD:
    case Token::BV_AND:
    case Token::BV_CONCAT:
    case Token::BV_MUL:
    case Token::BV_OR:
    case Token::BV_SUB:
    case Token::BV_XOR:
    case Token::FUN_APP:
    case Token::FORALL:
    case Token::EXISTS:
    case Token::FP_EQ:
    case Token::FP_GEQ:
    case Token::FP_GT:
    case Token::FP_LEQ:
    case Token::FP_LT: break;

    case Token::NOT:
    case Token::BV_NEG:
    case Token::BV_NOT:
    case Token::BV_REDOR:
    case Token::BV_REDAND:
    case Token::BV_REDXOR:
    case Token::FP_ABS:
    case Token::FP_IS_INF:
    case Token::FP_IS_NAN:
    case Token::FP_IS_NEG:
    case Token::FP_IS_NORMAL:
    case Token::FP_IS_POS:
    case Token::FP_IS_SUBNORMAL:
    case Token::FP_IS_ZERO:
    case Token::FP_NEG: n_args = 1; break;

    case Token::ARRAY_SELECT:
    case Token::BV_ASHR:
    case Token::BV_COMP:
    case Token::BV_LSHR:
    case Token::BV_NAND:
    case Token::BV_NOR:
    case Token::BV_SDIV:
    case Token::BV_SGE:
    case Token::BV_SGT:
    case Token::BV_SHL:
    case Token::BV_SLE:
    case Token::BV_SLT:
    case Token::BV_SMOD:
    case Token::BV_SREM:
    case Token::BV_UDIV:
    case Token::BV_UGE:
    case Token::BV_UGT:
    case Token::BV_ULE:
    case Token::BV_ULT:
    case Token::BV_UREM:
    case Token::BV_XNOR:
    case Token::BV_SADDO:
    case Token::BV_UADDO:
    case Token::BV_SDIVO:
    case Token::BV_SMULO:
    case Token::BV_UMULO:
    case Token::BV_SSUBO:
    case Token::BV_USUBO:
    case Token::FP_MAX:
    case Token::FP_MIN:
    case Token::FP_NAN:
    case Token::FP_REM:
    case Token::FP_RTI:
    case Token::FP_SQRT: n_args = 2; break;

    case Token::ARRAY_STORE:
    case Token::ITE:
    case Token::FP_FP:
    case Token::FP_ADD:
    case Token::FP_DIV:
    case Token::FP_MUL:
    case Token::FP_SUB: n_args = 3; break;

    case Token::FP_FMA: n_args = 4; break;

    case Token::BV_EXTRACT:
      n_args = 1;
      n_idxs = 2;
      break;

    case Token::BV_REPEAT:
    case Token::BV_ROTATE_LEFT:
    case Token::BV_ROTATE_RIGHT:
    case Token::BV_SIGN_EXTEND:
    case Token::BV_ZERO_EXTEND:
      n_args = 1;
      n_idxs = 1;
      break;

    case Token::FP_TO_SBV:
    case Token::FP_TO_UBV:
      n_args = 2;
      n_idxs = 1;
      break;

    case Token::FP_TO_FP:
    case Token::FP_TO_FP_UNSIGNED: n_idxs = 2; break;

    default: assert(false);
  }

  // check number of arguments
  assert(n_args > 0 || n_args == 0);
  size_t cnt_args = nargs() - n_idxs;
  if (n_args > 0)
  {
    if (cnt_args != n_args)
    {
      return error("expected " + std::to_string(n_args) + " argument"
                       + (n_args > 1 ? "s" : "") + " to '"
                       + std::to_string(token) + "', got "
                       + std::to_string(cnt_args),
                   item_open.d_coo);
    }
  }
  else if (token == Token::FP_TO_FP)
  {
    if (peek_is_str_arg())
    {
      if (cnt_args != 2 && cnt_args != 3)
      {
        return error("expected 2 arguments to '" + std::to_string(token)
                         + "', got " + std::to_string(cnt_args),
                     item_open.d_coo);
      }
    }
    else if (cnt_args != 1 && cnt_args != 2)
    {
      return error("expected 1 or 2 arguments to '" + std::to_string(token)
                       + "', got " + std::to_string(cnt_args),
                   item_open.d_coo);
    }
  }
  else if (token == Token::FP_TO_FP_UNSIGNED)
  {
    if (cnt_args != 2)
    {
      return error("expected 2 arguments to '" + std::to_string(token)
                       + "', got " + std::to_string(cnt_args - 2),
                   item_open.d_coo);
    }
  }
  else if (cnt_args < 2)
  {
    return error("expected at least 2 arguments to '" + std::to_string(token)
                     + "', got " + std::to_string(cnt_args),
                 item_open.d_coo);
  }

  // actual number of arguments
  n_args = cnt_args;

  // check arguments and indices and pop
  size_t idx_idxs = d_work_args_control.back();  // start index of indices
  size_t idx      = idx_idxs + n_idxs;           // start index of args
  assert(args.empty());
  args.resize(n_args);
  if (idxs)
  {
    assert(idxs->empty());
    idxs->resize(n_idxs);
  }

#ifndef NDEBUG
  for (size_t i = idx, n = idx + n_args; i < n; ++i)
  {
    assert(peek_is_term_arg(i));
  }
  for (size_t i = idx_idxs, n = idx_idxs + n_idxs; i < n; ++i)
  {
    assert(peek_is_uint64_arg(i));
  }
#endif

  switch (token)
  {
    case Token::DISTINCT:
    case Token::EQUAL:
      args[0] = peek_term_arg(idx);
      for (size_t i = 1, j = idx + i; i < n_args; ++i, ++j)
      {
        args[i] = peek_term_arg(j);
        if (args[i].sort() != args[i - 1].sort())
        {
          return error("expected terms of same sort at indices "
                           + std::to_string(i - 1) + " and " + std::to_string(i)
                           + " as argument to '" + std::to_string(token) + "'",
                       arg_coo(j));
        }
      }
      break;

    case Token::AND:
    case Token::IMPLIES:
    case Token::NOT:
    case Token::OR:
    case Token::XOR:
      for (size_t i = 0, j = idx; i < n_args; ++i, ++j)
      {
        args[i] = peek_term_arg(j);
        if (!args[i].sort().is_bool())
        {
          return error("expected Boolean term at index " + std::to_string(i)
                           + " as argument to '" + std::to_string(token) + "'",
                       arg_coo(j));
        }
      }
      break;

    case Token::ITE:
      args[0] = peek_term_arg(idx);
      args[1] = peek_term_arg(idx + 1);
      args[2] = peek_term_arg(idx + 2);
      if (!args[0].sort().is_bool())
      {
        return error("expected Boolean term at index 0 as argument to '"
                         + std::to_string(token) + "'",
                     arg_coo(idx));
      }
      if (args[1].sort() != args[2].sort())
      {
        return error(
            "expected terms of same sort at indices 1 and 2 as argument to '"
                + std::to_string(token) + "'",
            arg_coo(idx + 2));
      }
      break;

    case Token::ARRAY_SELECT:
      args[0] = peek_term_arg(idx);
      args[1] = peek_term_arg(idx + 1);
      if (!args[0].sort().is_array())
      {
        return error("expected array as first argument to '"
                         + std::to_string(token) + "'",
                     arg_coo(idx));
      }
      if (args[1].sort() != args[0].sort().array_index())
      {
        return error("index sort of array and sort of index do not match",
                     arg_coo(idx + 1));
      }
      break;
    case Token::ARRAY_STORE:
      args[0] = peek_term_arg(idx);
      args[1] = peek_term_arg(idx + 1);
      args[2] = peek_term_arg(idx + 2);
      if (!args[0].sort().is_array())
      {
        return error("expected array as first argument to '"
                         + std::to_string(token) + "'",
                     arg_coo(idx));
      }
      if (args[1].sort() != args[0].sort().array_index())
      {
        return error("index sort of array and sort of index do not match",
                     arg_coo(idx + 1));
      }
      if (args[2].sort() != args[0].sort().array_element())
      {
        return error("element sort of array and sort of element do not match",
                     arg_coo(idx + 2));
      }
      break;

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
    case Token::BV_USUBO:
      for (size_t i = 0, j = idx; i < n_args; ++i, ++j)
      {
        args[i] = peek_term_arg(j);
        if (!args[i].sort().is_bv())
        {
          return error("expected bit-vector term at index " + std::to_string(i)
                           + " as argument to '" + std::to_string(token) + "'",
                       arg_coo(j));
        }
        if (i > 0 && token != Token::BV_CONCAT)
        {
          if (args[i].sort() != args[i - 1].sort())
          {
            return error("expected terms of same sort at indices "
                             + std::to_string(i - 1) + " and "
                             + std::to_string(i) + " as argument to '"
                             + std::to_string(token) + "'",
                         arg_coo(j));
          }
        }
      }
      break;

    case Token::FP_FP:
      args[0] = peek_term_arg(idx);
      args[1] = peek_term_arg(idx + 1);
      args[2] = peek_term_arg(idx + 2);
      if (!args[0].sort().is_bv() || args[0].sort().bv_size() != 1)
      {
        return error(
            "expected bit-vector term of size 1 at index 0 as argument to '"
                + std::to_string(token) + "'",
            arg_coo(idx));
      }
      if (!args[1].sort().is_bv())
      {
        return error("expected bit-vector term at index 1 as argument to '"
                         + std::to_string(token) + "'",
                     arg_coo(idx + 1));
      }
      if (!args[2].sort().is_bv())
      {
        return error("expected bit-vector term at index 2 as argument to '"
                         + std::to_string(token) + "'",
                     arg_coo(idx + 2));
      }
      break;

    case Token::FP_ADD:
    case Token::FP_DIV:
    case Token::FP_FMA:
    case Token::FP_MUL:
    case Token::FP_RTI:
    case Token::FP_SQRT:
    case Token::FP_SUB:
    case Token::FP_TO_SBV:
    case Token::FP_TO_UBV: has_rm = true; [[fallthrough]];
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
    case Token::FP_NAN:
    case Token::FP_NEG:
    case Token::FP_NEG_INF:
    case Token::FP_NEG_ZERO:
    case Token::FP_POS_INF:
    case Token::FP_POS_ZERO:
    case Token::FP_REM:
    case Token::FP_ABS:
    case Token::FP_EQ:
      for (size_t i = 0, j = idx; i < n_args; ++i, ++j)
      {
        args[i] = peek_term_arg(j);
        if (has_rm && i == 0)
        {
          if (!args[0].sort().is_rm())
          {
            return error(
                "expected rounding-mode term at index 0 as argument to '"
                    + std::to_string(token) + "'",
                arg_coo(j));
          }
        }
        else
        {
          if (!args[i].sort().is_fp())
          {
            return error("expected floating-point term at index "
                             + std::to_string(i) + " as argument to '"
                             + std::to_string(token) + "'",
                         arg_coo(j));
          }
        }
        if ((!has_rm && i > 0) || (has_rm && i > 1))
        {
          if (args[i].sort() != args[i - 1].sort())
          {
            return error("expected terms of same sort at indices "
                             + std::to_string(i - 1) + " and "
                             + std::to_string(i) + " as argument to '"
                             + std::to_string(token) + "'",
                         arg_coo(j));
          }
        }
      }
      break;

    case Token::FP_TO_FP_UNSIGNED:
    case Token::FP_TO_FP:
      args[0] = peek_term_arg(idx);
      if (n_args == 1)
      {
        if (!args[0].sort().is_bv())
        {
          return error("expected bit-vector term at index 0 as argument to '"
                           + std::to_string(token) + "'",
                       arg_coo(idx));
        }
        break;
      }
      if (!args[0].sort().is_rm())
      {
        return error("expected rounding-mode term at index 0 as argument to '"
                         + std::to_string(token) + "'",
                     arg_coo(idx));
      }
      if (peek_is_str_arg(idx + 1))
      {
        assert(strs);
        assert(strs->empty());
        strs->resize(cnt_args - 1);
        // ((_ to_fp eb sb) RoundingMode Real)
        (*strs)[0] = peek_str_arg(idx + 1);
        if (cnt_args == 3)
        {
          (*strs)[1] = peek_str_arg(idx + 2);
        }
      }
      else
      {
        // ((_ to_fp eb sb) RoundingMode (_ FloatingPoint eb sb))
        // ((_ to_fp eb sb) RoundingMode (_ BitVec m))
        // ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m))
        if (!peek_is_term_arg(idx + 1))
        {
          return error_arg("expected term as argument at index 1 to '"
                           + std::to_string(token) + "'");
        }
        args[1] = peek_term_arg(idx + 1);
        if (!args[1].sort().is_bv() && !args[1].sort().is_fp())
        {
          return error_arg(
              "expected bit-vector or floating-point term at index 1 as "
              "argument "
              "to '"
              + std::to_string(token) + "'");
        }
      }
      break;

    case Token::FUN_APP: {
      for (size_t i = 0, j = idx; i < n_args; ++i, ++j)
      {
        args[i] = peek_term_arg(j);
      }
      args[0] = peek_term_arg(idx);  // fun
      assert(!args[0].is_null());
      if (!args[0].sort().is_fun())
      {
        return error("expected fun", arg_coo(idx));
      }
      size_t arity = args[0].sort().fun_arity();
      if (n_args - 1 != arity)
      {
        return error("expected " + std::to_string(arity) + " arguments to '"
                         + std::to_string(token) + "', got "
                         + std::to_string(n_args - 1),
                     item_open.d_coo);
      }
      const std::vector<bitwuzla::Sort>& domain = args[0].sort().fun_domain();
      assert(domain.size() == arity);
      for (size_t i = 1; i < arity; ++i)
      {
        if (domain[i - 1] != args[i].sort())
        {
          return error("expected term of sort '" + domain[i].str() + "', got "
                           + args[i].sort().str(),
                       arg_coo(idx + i));
        }
      }
    }
    break;

    case Token::FORALL:
    case Token::EXISTS: {
      for (size_t i = 0, j = idx; i < n_args; ++i, ++j)
      {
        args[i] = peek_term_arg(j);
        if (i < n_args - 1)
        {
          if (!args[i].is_variable())
          {
            return error("expected variable at index " + std::to_string(i)
                             + " as argument to '"
                             + std::to_string(item_open.d_token) + "'",
                         arg_coo(j));
          }
        }
        else
        {
          if (!args[i].sort().is_bool())
          {
            return error("expected Boolean term as body to '"
                             + std::to_string(item_open.d_token) + "'",
                         arg_coo(j));
          }
        }
      }
    }
    break;

    default: assert(false);
  }

  for (size_t i = 0, j = idx_idxs; i < n_idxs; ++i, ++j)
  {
    assert(idxs);
    if (!peek_is_uint64_arg(j))
    {
      return error("expected integer argument at index " + std::to_string(idx)
                       + " to '" + std::to_string(item_open.d_token) + "'",
                   arg_coo(j));
    }
    (*idxs)[i] = peek_uint64_arg(j);
  }
  if (token == Token::BV_EXTRACT)
  {
    if ((*idxs)[0] >= args[0].sort().bv_size())
    {
      return error("upper index '" + std::to_string((*idxs)[0])
                       + "' too high for bit-vector of size "
                       + std::to_string(args[0].sort().bv_size())
                       + " as argument to '" + std::to_string(token) + "'",
                   arg_coo(idx_idxs));
    }
    if ((*idxs)[0] < (*idxs)[1])
    {
      return error("upper index must be >= lower index as argument to '"
                       + std::to_string(token) + "'",
                   arg_coo(idx_idxs));
    }
  }
  else if (token == Token::BV_REPEAT)
  {
    if (((uint64_t) (UINT64_MAX / (*idxs)[0])) < args[0].sort().bv_size())
    {
      return error(
          "index '" + std::to_string((*idxs)[0]) + "' as argument to '"
              + std::to_string(token)
              + "' too large, resulting bit-vector size exceeds maximum "
              + "bit-vector size of " + std::to_string(UINT64_MAX),
          arg_coo(idx_idxs));
    }
  }
  else if (token == Token::BV_SIGN_EXTEND || token == Token::BV_ZERO_EXTEND)
  {
    if ((*idxs)[0] > UINT64_MAX - args[0].sort().bv_size())
    {
      return error(
          "index '" + std::to_string((*idxs)[0]) + "' as argument to '"
              + std::to_string(token)
              + "' too large, resulting bit-vector size exceeds maximum "
              + "bit-vector size of " + std::to_string(UINT64_MAX),
          arg_coo(idx_idxs));
    }
  }
  else if (token == Token::FP_TO_FP && args[0].sort().is_bv())
  {
    if (args[0].sort().bv_size() != (*idxs)[0] + (*idxs)[1])
    {
      return error("size of bit-vector term '"
                   + std::to_string(args[0].sort().bv_size())
                   + " does not match floating-point format '"
                   + std::to_string((*idxs)[0]) + " "
                   + std::to_string((*idxs)[1]) + "'");
    }
  }

  d_work_args.resize(d_work_args.size() - n_args - n_idxs);
  d_work_args_coo.resize(d_work_args_coo.size() - n_args - n_idxs);
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
