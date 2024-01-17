/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/smt2/parser.h"

#include <iostream>

namespace bzla {
namespace parser::smt2 {

/* Parser public ------------------------------------------------------------ */

Parser::Parser(bitwuzla::Options& options,
               const std::string& infile_name,
               std::ostream* out)
    : bzla::parser::Parser(options, infile_name, out), d_decls(nullptr)
{
  if (d_error.empty())
  {
    d_lexer.reset(new Lexer(d_infile));
  }
  if (infile_name == "<stdin>")
  {
    d_lexer->d_buf_size = 1;
    d_lexer->d_buf_idx  = 1;
  }
  d_token_class_mask = static_cast<uint32_t>(TokenClass::COMMAND)
                       | static_cast<uint32_t>(TokenClass::CORE)
                       | static_cast<uint32_t>(TokenClass::KEYWORD)
                       | static_cast<uint32_t>(TokenClass::RESERVED);
  d_work_control.push_back(0);
}

Parser::Parser(bitwuzla::Options& options,
               const std::string& infile_name,
               FILE* infile,
               std::ostream* out)
    : bzla::parser::Parser(options, infile_name, infile, out), d_decls(nullptr)
{
  if (d_error.empty())
  {
    d_lexer.reset(new Lexer(d_infile));
  }
  if (infile_name == "<stdin>")
  {
    d_lexer->d_buf_size = 1;
    d_lexer->d_buf_idx  = 1;
  }
  d_token_class_mask = static_cast<uint32_t>(TokenClass::COMMAND)
                       | static_cast<uint32_t>(TokenClass::CORE)
                       | static_cast<uint32_t>(TokenClass::KEYWORD)
                       | static_cast<uint32_t>(TokenClass::RESERVED);
  d_work_control.push_back(0);
}

std::string
Parser::parse(bool parse_only)
{
  util::Timer timer(d_statistics.time_parse);

  Log(2) << "parse " << d_infile_name;

  if (!d_error.empty())
  {
    return d_error;
  }

  while (parse_command(parse_only) && !d_done && !terminate())
    ;

  // init in case that we didn't parse any commands that triggered init
  init_bitwuzla();

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
         << ((double) d_statistics.time_parse.elapsed() / 1000) << " seconds";
  return d_error;
}

/* Parser private ----------------------------------------------------------- */

bool
Parser::parse_command(bool parse_only)
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
    return error("expected command at '" + std::string(d_lexer->token()) + "'");
  }
  push_item(token, d_lexer->coo());

  Log(2) << "parse command '" << token << "'";

  bool res = false;
  switch (token)
  {
    case Token::ASSERT: res = parse_command_assert(); break;
    case Token::CHECK_SAT: res = parse_command_check_sat(parse_only); break;
    case Token::CHECK_SAT_ASSUMING:
      res = parse_command_check_sat(parse_only, true);
      break;
    case Token::DECLARE_CONST: res = parse_command_declare_fun(true); break;
    case Token::DECLARE_SORT: res = parse_command_declare_sort(); break;
    case Token::DECLARE_FUN: res = parse_command_declare_fun(); break;
    case Token::DEFINE_FUN: res = parse_command_define_fun(); break;
    case Token::DEFINE_SORT: res = parse_command_define_sort(); break;
    case Token::ECHO: res = parse_command_echo(); break;
    case Token::EXIT: res = parse_command_exit(); break;
    case Token::GET_MODEL: res = parse_command_get_model(); break;
    case Token::GET_UNSAT_ASSUMPTIONS:
      res = parse_command_get_unsat_assumptions();
      break;
    case Token::GET_UNSAT_CORE: res = parse_command_get_unsat_core(); break;
    case Token::GET_VALUE: res = parse_command_get_value(); break;
    case Token::POP: res = parse_command_pop(); break;
    case Token::PUSH: res = parse_command_push(); break;
    case Token::RESET: res = parse_command_reset(); break;
    case Token::RESET_ASSERTIONS: res = parse_command_reset_assertions(); break;
    case Token::SET_INFO: res = parse_command_set_info(); break;
    case Token::SET_LOGIC: res = parse_command_set_logic(); break;
    case Token::SET_OPTION: res = parse_command_set_option(); break;

    default:
      assert(d_lexer->has_token());
      return error("unsupported command '" + std::string(d_lexer->token())
                   + "'");
  }
  d_work.pop_back();
  d_statistics.num_commands += 1;
  return res;
}

bool
Parser::parse_command_assert()
{
  init_logic();
  init_bitwuzla();
  d_record_named_assertions = true;
  Token la = next_token();
  if (!parse_term(true, la))
  {
    return false;
  }
  if (!peek_is_term_arg())
  {
    return error("expected term");
  }
  if (!peek_term_arg().sort().is_bool())
  {
    return error_arg("asserted term is not a formula");
  }
  bitwuzla::Term term = pop_term_arg();
  if (!parse_rpar())
  {
    return false;
  }
  d_bitwuzla->assert_formula(term);
  print_success();
  d_statistics.num_assertions += 1;
  d_record_named_assertions = false;
  return true;
}

bool
Parser::parse_command_check_sat(bool parse_only, bool with_assumptions)
{
  init_logic();
  init_bitwuzla();
  d_assumptions.clear();
  if (with_assumptions)
  {
    if (!parse_lpar())
    {
      return false;
    }
    std::vector<bitwuzla::Term> assumptions;
    std::vector<std::string> assumptions_strs;
    if (!parse_term_list(assumptions, &assumptions_strs))
    {
      return false;
    }
    assert(assumptions.size() == assumptions_strs.size());
    for (size_t i = 0, n = assumptions.size(); i < n; ++i)
    {
      if (!assumptions[i].sort().is_bool())
      {
        return error_arg("assumption at index " + std::to_string(i)
                         + " is not a formula");
      }
      d_assumptions.emplace(assumptions[i], assumptions_strs[i]);
    }
    if (!parse_rpar())
    {
      return false;
    }
    if (!parse_only)
    {
      d_result = d_bitwuzla->check_sat(assumptions);
    }
  }
  else
  {
    if (!parse_rpar())
    {
      return false;
    }
    if (!parse_only)
    {
      d_result = d_bitwuzla->check_sat();
    }
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
  else if (!parse_only)
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

  bitwuzla::Sort sort;
  std::vector<bitwuzla::Sort> domain;
  if (!is_const)
  {
    if (!parse_lpar())
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
      if (!parse_sort(sort, true, la))
      {
        return false;
      }
      domain.emplace_back(sort);
    }
  }

  if (!parse_sort(sort))
  {
    return false;
  }

  if (domain.size())
  {
    symbol->d_term = bitwuzla::mk_const(bitwuzla::mk_fun_sort(domain, sort),
                                        symbol->d_symbol);
  }
  else
  {
    symbol->d_term = bitwuzla::mk_const(sort, symbol->d_symbol);
  }
  if (!parse_rpar())
  {
    return false;
  }
  d_decls.push_back(symbol);
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
                     + "' already defined at line "
                     + std::to_string(peek_node_arg()->d_coo.line) + " column "
                     + std::to_string(peek_node_arg()->d_coo.col));
  }
  SymbolTable::Node* symbol = pop_node_arg(true);
  uint64_t uint;
  if (!parse_uint64(uint))
  {
    return false;
  }
  if (uint != 0)
  {
    return error("'declare-sort' of arity > 0 not supported");
  }
  symbol->d_sort = bitwuzla::mk_uninterpreted_sort(symbol->d_symbol);
  if (!parse_rpar())
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
                     + "' already defined at line "
                     + std::to_string(peek_node_arg()->d_coo.line) + " column "
                     + std::to_string(peek_node_arg()->d_coo.col));
  }
  SymbolTable::Node* symbol = pop_node_arg(true);

  if (!parse_lpar())
  {
    return false;
  }

  bitwuzla::Sort sort;
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
    if (!parse_sort(sort))
    {
      return false;
    }
    parse_rpar();
    symbol->d_term = bitwuzla::mk_var(sort, symbol->d_symbol);
    args.emplace_back(symbol->d_term);
  }

  if (!parse_sort(sort))
  {
    return false;
  }

  if (!parse_term())
  {
    return false;
  }

  bitwuzla::Term body = pop_term_arg();
  if (body.sort() != sort)
  {
    return error_arg("expected term of sort '" + sort.str() + "' but got '"
                     + body.sort().str());
  }

  if (args.size())
  {
    args.emplace_back(body);
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

  if (!parse_rpar())
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
                     + "' already defined at line "
                     + std::to_string(peek_node_arg()->d_coo.line) + " column "
                     + std::to_string(peek_node_arg()->d_coo.col));
  }
  SymbolTable::Node* symbol = pop_node_arg(true);

  if (!parse_lpar())
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

  if (!parse_sort(symbol->d_sort))
  {
    return false;
  }

  if (!parse_rpar())
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

  if (!parse_rpar())
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
  if (!parse_rpar())
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
  if (!parse_rpar())
  {
    return false;
  }
  if (!d_options.get(bitwuzla::Option::PRODUCE_MODELS))
  {
    return error("model generation is not enabled");
  }
  if (d_result != bitwuzla::Result::SAT)
  {
    return true;
  }
  std::stringstream ss;
  ss << "(" << std::endl;
  for (const auto& node : d_decls)
  {
    ss << "  (define-fun " << node->d_symbol << " (";
    const bitwuzla::Term& term = node->d_term;
    const bitwuzla::Sort& sort = term.sort();
    if (sort.is_fun())
    {
      bitwuzla::Term value = d_bitwuzla->get_value(term);
      assert(value.kind() == bitwuzla::Kind::LAMBDA);
      assert(value.num_children() == 2);
      size_t i = 0;
      while (value[1].kind() == bitwuzla::Kind::LAMBDA)
      {
        assert(value[0].is_variable());
        ss << (i > 0 ? " " : "") << "(" << value[0] << " " << value[0].sort()
           << ") ";
        value = value[1];
        i += 1;
      }
      assert(value[0].is_variable());
      ss << (i > 0 ? " " : "") << "(" << value[0] << " " << value[0].sort()
         << ")) " << sort.fun_codomain() << " ";
      ss << value[1] << ")" << std::endl;
    }
    else
    {
      ss << ") " << sort << " " << d_bitwuzla->get_value(node->d_term) << ")"
         << std::endl;
    }
  }
  ss << ")" << std::endl;
  (*d_out) << ss.str();
  d_out->flush();
  return true;
}

bool
Parser::parse_command_get_unsat_assumptions()
{
  init_logic();
  init_bitwuzla();
  if (!parse_rpar())
  {
    return false;
  }
  if (d_result != bitwuzla::Result::UNSAT)
  {
    return true;
  }
  (*d_out) << "(";
  auto unsat_ass = d_bitwuzla->get_unsat_assumptions();
  for (size_t i = 0, n = unsat_ass.size(); i < n; ++i)
  {
    auto it = d_assumptions.find(unsat_ass[i]);
    (*d_out) << (i > 0 ? " " : "") << it->second;
  }
  (*d_out) << ")" << std::endl;
  d_out->flush();
  return true;
}

bool
Parser::parse_command_get_unsat_core()
{
  init_logic();
  init_bitwuzla();
  if (!parse_rpar())
  {
    return false;
  }
  if (!d_options.get(bitwuzla::Option::PRODUCE_UNSAT_CORES))
  {
    return error("unsat core production is not enabled");
  }
  if (d_result != bitwuzla::Result::UNSAT)
  {
    return true;
  }
  (*d_out) << "(";
  auto unsat_core = d_bitwuzla->get_unsat_core();
  for (size_t i = 0, n = unsat_core.size(); i < n; ++i)
  {
    auto it = d_named_assertions.find(unsat_core[i]);
    if (it != d_named_assertions.end())
    {
      (*d_out) << (i > 0 ? " " : "") << it->second->d_symbol;
    }
  }
  (*d_out) << ")" << std::endl;
  d_out->flush();
  return true;
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
  if (!parse_lpar())
  {
    return false;
  }
  std::vector<bitwuzla::Term> args;
  std::vector<std::string> repr;
  if (!parse_term_list(args, &repr))
  {
    return false;
  }
  assert(args.size() == repr.size());
  if (!parse_rpar())
  {
    return false;
  }
  if (d_result != bitwuzla::Result::SAT)
  {
    return true;
  }
  (*d_out) << "(";
  size_t size_args = args.size();
  std::stringstream ss;
  if (size_args > 1)
  {
    ss << std::endl << "  ";
  }
  const std::string& pref = ss.str();
  for (size_t i = 0; i < size_args; ++i)
  {
    (*d_out) << pref;
    (*d_out) << "(";
    (*d_out) << repr[i] << " " << d_bitwuzla->get_value(args[i]);
    (*d_out) << ")";
  }
  if (size_args > 1)
  {
    (*d_out) << std::endl;
  }
  (*d_out) << ")" << std::endl;
  d_out->flush();
  return true;
}

bool
Parser::parse_command_pop()
{
  init_logic();
  init_bitwuzla();

  uint64_t nlevels;
  if (!parse_uint64(nlevels))
  {
    return false;
  }
  if (!parse_rpar())
  {
    return false;
  }
  if (nlevels > d_assertion_level)
  {
    return error_arg("attempting to pop '" + std::to_string(nlevels)
                     + "' but only '" + std::to_string(nlevels)
                     + "' have been pushed previously");
  }

  if (!d_global_decl)
  {
    // remove symbols from current scope
    for (size_t i = 0; i < nlevels; ++i)
    {
      d_table.pop_level(d_assertion_level);
      d_assertion_level -= 1;
      d_decls.pop();
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

  uint64_t nlevels;
  if (!parse_uint64(nlevels))
  {
    return false;
  }
  if (!parse_rpar())
  {
    return false;
  }
  d_assertion_level += nlevels;
  d_bitwuzla->push(nlevels);
  if (!d_global_decl)
  {
    for (uint64_t i = 0; i < nlevels; ++i)
    {
      d_decls.push();
    }
  }
  print_success();
  return true;
}

bool
Parser::parse_command_reset()
{
  init_logic();

  if (!parse_rpar())
  {
    return false;
  }
  d_bitwuzla.reset();
  d_table.reset();
  d_options = d_options_orig;
  print_success();
  return true;
}

bool
Parser::parse_command_reset_assertions()
{
  init_logic();

  if (!parse_rpar())
  {
    return false;
  }
  d_bitwuzla.reset();
  if (!d_global_decl)
  {
    d_table.reset();
  }
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
      return error("invalid value '" + std::string(d_lexer->token())
                   + "' for ':status'");
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
  if (parse_rpar())
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
    }
    else if (token == Token::FALSE)
    {
      d_print_success = false;
    }
    else
    {
      assert(d_lexer->has_token());
      return error("expected Boolean argument at '"
                   + std::string(d_lexer->token()) + "'");
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
      return error("expected Boolean argument at '"
                   + std::string(d_lexer->token()) + "'");
    }
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
    std::string opt = d_lexer->token() + 1;
    (void) next_token();
    assert(d_lexer->has_token());
    if (!d_options.is_valid(opt))
    {
      Msg(1) << "warning: unsupported option '" << opt << "'";
    }
    else
    {
      try
      {
        const char* value = d_lexer->token();
        if (d_options.is_mode(d_options.option(opt.c_str())))
        {
          size_t len = strlen(value);
          if (value[0] != '"' || value[len - 1] != '"')
          {
            return error("expected string argument to option '" + opt + "'");
          }
          d_options.set(opt, std::string(value + 1, len - 2));
        }
        else
        {
          d_options.set(opt, value);
        }
      }
      catch (bitwuzla::Exception& e)
      {
        return error(e.msg());
      }
      if (opt == d_options.lng(bitwuzla::Option::VERBOSITY))
      {
        uint64_t level = d_options.get(bitwuzla::Option::VERBOSITY);
        d_verbosity    = level;
        d_logger.set_verbosity_level(level);
      }
    }
  }
  if (parse_rpar())
  {
    print_success();
    return true;
  }
  return false;
}

/* -------------------------------------------------------------------------- */

bool
Parser::parse_uint64(uint64_t& uint)
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
      uint = std::stoull(d_lexer->token());
      return true;
    }
    catch (...)
    {
      return error("invalid 64 bit integer '" + std::string(d_lexer->token())
                   + "'");
    }
  }
  return error("expected 64 bit integer");
}

bool
Parser::parse_symbol(const std::string& error_msg,
                     bool shadow,
                     bool insert,
                     bool look_ahead,
                     Token la)
{
  Token token = look_ahead ? la : next_token(insert);
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
    if (insert)
    {
      d_last_node = d_table.insert(token, d_lexer->token(), d_assertion_level);
    }
    else
    {
      d_last_node =
          new SymbolTable::Node(token, d_lexer->token(), d_assertion_level);
    }
    assert(d_last_node->has_symbol());
    d_last_node->d_coo = d_lexer->coo();
  }
  push_item(token, d_last_node, d_lexer->coo());
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
  } while (nopen() > 0);
  assert(d_work.size() > 0);
  return true;
}

bool
Parser::parse_term_list(std::vector<bitwuzla::Term>& terms,
                        std::vector<std::string>* repr)
{
  terms.clear();
  for (;;)
  {
    d_save_repr = true;
    d_repr.clear();

    Token la = next_token();
    if (!check_token(la))
    {
      return false;
    }
    if (la == Token::RPAR)
    {
      d_save_repr = false;
      break;
    }
    if (!parse_term(true, la))
    {
      return false;
    }
    d_save_repr = false;
    if (repr)
    {
      repr->emplace_back(d_repr);
    }
    terms.emplace_back(pop_term_arg());
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
      push_item(Token::LETBIND, d_lexer->coo());
      d_is_var_binding          = false;
      if (!parse_symbol("", true, false))
      {
        return false;
      }
      assert(peek_is_node_arg());
      peek_node_arg()->d_coo = d_lexer->coo();
    }
    else if (d_is_sorted_var)
    {
      // parse <sorted_var>: <symbol> <sort>
      push_item(Token::SORTED_VAR, d_lexer->coo());
      d_is_sorted_var           = false;
      if (!parse_symbol("in sorted var", true))
      {
        return false;
      }
      peek_node_arg()->d_coo = d_lexer->coo();
      bitwuzla::Sort sort;
      if (!parse_sort(sort))
      {
        return false;
      }
      SymbolTable::Node* symbol = peek_node_arg();
      assert(symbol->has_symbol());
      symbol->d_term = bitwuzla::mk_var(sort, symbol->d_symbol);
      set_item(d_work.back(), Token::TERM, symbol->d_term);
    }
  }
  else if (d_is_var_binding)
  {
    return error("expected variable binding");
  }
  else if (d_is_sorted_var)
  {
    return error("expected sorted variable");
  }
  else if (token == Token::NAMED)
  {
    d_skip_attribute_value = false;
    push_item(Token::SYMBOL, d_last_node, d_lexer->coo());
    if (!parse_symbol("as attribute value to :named", false))
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
  else if (token == Token::ATTRIBUTE && item_open().d_token == Token::BANG)
  {
    // Catch-all for all unsupported annotation attributes, we ignore the
    // value of unsupported annotation attributes. For this, we have to ignore
    // undefined symbols that occur as value in '<attribute> <value>' in
    // parse_open_term_symbol(). If the attribute value is not a symbol but a
    // parentheses-enclosed term (e.g., (bvadd x y)), however, we require that
    // any symbols that occur in that term are defined.
    push_item(Token::SYMBOL, d_last_node, d_lexer->coo());
    d_skip_attribute_value = true;
  }
  else if (is_symbol(token))
  {
    if (token == Token::SYMBOL)
    {
      assert(d_last_node);
      push_item(token, d_last_node, d_lexer->coo());
    }
    else
    {
      push_item(token, d_lexer->coo());
    }
    if (!parse_open_term_symbol())
    {
      return false;
    }
  }
  else if (token == Token::BINARY_VALUE)
  {
    assert(d_lexer->has_token());
    std::string val     = d_lexer->token() + 2;
    bitwuzla::Sort sort = bitwuzla::mk_bv_sort(val.size());
    push_item(Token::TERM, bitwuzla::mk_bv_value(sort, val), d_lexer->coo());
  }
  else if (token == Token::HEXADECIMAL_VALUE)
  {
    assert(d_lexer->has_token());
    std::string val     = d_lexer->token() + 2;
    bitwuzla::Sort sort = bitwuzla::mk_bv_sort(val.size() * 4);
    push_item(
        Token::TERM, bitwuzla::mk_bv_value(sort, val, 16), d_lexer->coo());
  }
  else if (token == Token::DECIMAL_VALUE || token == Token::REAL_VALUE)
  {
    assert(d_lexer->has_token());
    ParsedItem& item = item_open();
    item.d_strs.emplace_back(d_lexer->token());
    item.d_strs_coo.emplace_back(d_lexer->coo());
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
    bitwuzla::Sort sort;
    if (!parse_sort(sort))
    {
      return false;
    }
    if (!sort.is_array())
    {
      return error("expected array sort");
    }
    if (!parse_rpar())
    {
      return false;
    }
    // ((as const(-array) <sort>) <term>) -> (as const(-array) sort term)
    if (idx_open() < 2 || d_work[idx_open() - 2].d_token != Token::LPAR)
    {
      return error("missing '(' before '(as'", d_work.back().d_coo);
    }
    // store sort in AS item
    assert(item_open().d_token == Token::AS);
    set_item(item_open(), item_open().d_token, sort);
    assert(d_work[idx_open() - 1].d_token == Token::LPAR);
    d_work.erase(d_work.begin() + idx_open() - 1);
    d_work_control.pop_back();
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

  ParsedItem& item        = item_open();
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
    case Token::FP_NOTANUMBER:
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
      if (val.size() < 2 || (val[0] != 'b' && val[1] != 'v'))
      {
        return error("invalid indexed term '" + val + "'");
      }
      std::string v = val.substr(2);
      if (!std::all_of(
              v.begin(), v.end(), [](char c) { return std::isdigit(c); }))
      {
        return error("invalid bit-vector value '" + val + "'");
      }
      item.d_strs.emplace_back(v);
      item.d_strs_coo.emplace_back(d_lexer->coo());
    }
    break;

    default:
      return error("expected identifier, got '" + std::string(d_lexer->token())
                   + "'");
  }

  for (uint64_t i = 0; i < nidxs; ++i)
  {
    uint64_t idx;
    if (!parse_uint64(idx))
    {
      return false;
    }
    if (min > idx)
    {
      if (idx == 0)
      {
        return error("expected non-zero index");
      }
      return error("expected index > " + std::to_string(min - 1) + ", got '"
                   + std::to_string(idx) + "'");
    }
    item.d_uints.push_back(idx);
    item.d_uints_coo.emplace_back(d_lexer->coo());
  }

  if (!parse_rpar())
  {
    return false;
  }

  if (kind == bitwuzla::Kind::VALUE)
  {
    bitwuzla::Term term;
    switch (token_kind)
    {
      case Token::FP_NOTANUMBER:
      case Token::FP_NEG_INF:
      case Token::FP_NEG_ZERO:
      case Token::FP_POS_INF:
      case Token::FP_POS_ZERO: {
        assert(item.d_uints.size() == 2);
        bitwuzla::Sort sort =
            bitwuzla::mk_fp_sort(item.d_uints[0], item.d_uints[1]);
        if (token_kind == Token::FP_NOTANUMBER)
        {
          term = bitwuzla::mk_fp_nan(sort);
        }
        else if (token_kind == Token::FP_NEG_INF)
        {
          term = bitwuzla::mk_fp_neg_inf(sort);
        }
        else if (token_kind == Token::FP_POS_INF)
        {
          term = bitwuzla::mk_fp_pos_inf(sort);
        }
        else if (token_kind == Token::FP_NEG_ZERO)
        {
          term = bitwuzla::mk_fp_neg_zero(sort);
        }
        else if (token_kind == Token::FP_POS_ZERO)
        {
          term = bitwuzla::mk_fp_pos_zero(sort);
        }
      }
      break;

      default: {
        assert(token_kind == Token::BV_VALUE);
        assert(item.d_uints.size() == 1);
        assert(item.d_strs.size() == 1);
        bitwuzla::Sort sort = bitwuzla::mk_bv_sort(item.d_uints[0]);
        term                = bitwuzla::mk_bv_value(sort, item.d_strs[0], 10);
      }
    }
    assert(d_work.back().d_token == Token::UNDERSCORE);
    d_work.pop_back();
    close_term_scope(term);
  }
  else
  {
    assert(node);
    assert(token_kind != Token::SYMBOL);
    size_t idx = idx_open();
    assert(d_work[idx].d_token == Token::UNDERSCORE);
    if (idx < 2 || d_work[idx - 2].d_token != Token::LPAR)
    {
      return error("missing '(' before '(_'", d_work[idx - 1].d_coo);
    }
    // ((_ <indexed_op> <idxs>) <terms>) -> (<indexed_op> <idxs> <terms>)
    d_work[idx].d_token = token_kind;
    d_work[idx].d_item  = node;
    d_work[idx].d_coo   = coo;
    d_work.erase(d_work.begin() + idx - 1);
    d_work_control.pop_back();
  }
  return true;
}

bool
Parser::parse_open_term_quant()
{
  if (!parse_lpar())
  {
    return false;
  }
  open_term_scope();
  push_item(Token::SORTED_VARS, d_lexer->coo());
  assert(!d_is_sorted_var);
  d_is_sorted_var = true;
  return true;
}

bool
Parser::parse_open_term_symbol()
{
  assert(!d_work.empty());

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
      if (!parse_lpar())
      {
        return false;
      }
      open_term_scope();
      push_item(Token::PARLETBIND, d_lexer->coo());
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
      if (!peek_item_is_token(Token::LPAR, d_work.size() - 2))
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
      if (d_work[d_work.size() - 2].d_token != Token::LPAR)
      {
        return error("missing '(' before '" + std::to_string(token) + "'");
      }
    }
    else
    {
      return error("unsupported reserved word '" + std::to_string(token) + "'");
    }
  }
  else if (token == Token::SYMBOL)
  {
    SymbolTable::Node* node = std::get<SymbolTable::Node*>(cur.d_item);
    assert(node);
    d_work.pop_back();
    if (d_skip_attribute_value && item_open().d_token == Token::BANG)
    {
      push_item(Token::SYMBOL, node, d_lexer->coo());
    }
    else
    {
      if (node->d_term.is_null())
      {
        assert(node->has_symbol());
        return error("undefined symbol '" + node->d_symbol + "'");
      }
      assert(!node->d_term.is_null());
      if (!node->d_term.sort().is_fun())
      {
        if (d_work.size() && d_work.back().d_token == Token::LPAR)
        {
          return error("unexpected function application, '" + node->d_symbol
                       + "' is not a function");
        }
      }
      else
      {
        push_item(Token::FUN_APP, d_lexer->coo());
      }
      push_item(Token::TERM, node->d_term, d_lexer->coo());
    }
  }
  else if (token == Token::TRUE)
  {
    set_item(cur, Token::TERM, bitwuzla::mk_true());
  }
  else if (token == Token::FALSE)
  {
    set_item(cur, Token::TERM, bitwuzla::mk_false());
  }
  else if (token == Token::ATTRIBUTE)
  {
    assert(d_lexer->has_token());
    return error("unexpected attribute '" + std::string(d_lexer->token())
                 + "'");
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
        && !peek_item_is_token(Token::FP_TO_FP, idx_prev()))
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
        set_item(cur,
                 Token::TERM,
                 bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNA));
      }
      else if (token == Token::FP_RM_RNE_LONG || token == Token::FP_RM_RNE)
      {
        set_item(cur,
                 Token::TERM,
                 bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNE));
      }
      else if (token == Token::FP_RM_RTN_LONG || token == Token::FP_RM_RTN)
      {
        set_item(cur,
                 Token::TERM,
                 bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTN));
      }
      else if (token == Token::FP_RM_RTP_LONG || token == Token::FP_RM_RTP)
      {
        set_item(cur,
                 Token::TERM,
                 bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTP));
      }
      else if (token == Token::FP_RM_RTZ_LONG || token == Token::FP_RM_RTZ)
      {
        set_item(cur,
                 Token::TERM,
                 bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTZ));
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
  if (!nopen())
  {
    return error("expected expression");
  }

  assert(d_work.size());
  ParsedItem& item      = item_open();
  Token token           = item.d_token;
  Lexer::Coordinate coo = item.d_coo;

  if (token == Token::OPEN)
  {
    assert(nargs() == 0);
    return error("unexpected '()'", coo);
  }

  if (token == Token::TERM)
  {
    return error("missing identifier, invalid term", coo);
  }

  if (d_expect_body)
  {
    return error("missing body to '" + std::to_string(token));
  }

  bool res = false;
  switch (token)
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
    case Token::BV_NEGO:
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
    case Token::BV_DEC:
    case Token::BV_INC:
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
    case Token::FP_NOTANUMBER:
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
      return error("unsupported term kind '" + std::to_string(token) + "'");
  }

  if (res)
  {
    if (idx_open() == 0 || d_work[idx_open() - 1].d_token != Token::LPAR)
    {
      return error("missing '(' before '" + std::to_string(token) + "'", coo);
    }

    if (token == Token::SORTED_VARS)
    {
      // this needs special handling, we leave the sorted_var terms as
      // arguments on the stack but have to close SORTED_VARS, e.g.,
      // (forall (<sorted_var> <sorted_var>) <body>) ->
      // (forall <sorted_var> <sorted_var> <body>)
      d_work.erase(d_work.begin() + idx_open() - 1);
      d_work_control.pop_back();
    }
    else if (token == Token::LETBIND)
    {
      // this needs special handling since we have to keep the symbols
      // bound by the let on the stack in order to be able to remove
      // them from the symbol table when closing the let
      assert(peek_is_node_arg());
      SymbolTable::Node* symbol = pop_node_arg();
      assert(peek_item_is_token(Token::LETBIND));
      d_work.pop_back();
      d_work_control.pop_back();
      assert(peek_item_is_token(Token::LPAR));
      set_item(d_work.back(), Token::SYMBOL, symbol);
    }
    else if (token == Token::PARLETBIND)
    {
      // this needs special handling since we have to keep the symbols
      // bound by the let on the stack in order to be able to remove
      // them from the symbol table when closing the let
      size_t idx = idx_open();
      assert(peek_item_is_token(Token::PARLETBIND, idx));
      assert(peek_item_is_token(Token::LPAR, idx - 1));
      // the var bindings of the current PARLETBIND are not yet inserted in the
      // symbol table since they may only be used (and thus inserted) after
      // binding all of them in parallel, we have to insert them now
      for (size_t i = idx + 1; i < d_work.size(); ++i)
      {
        d_table.insert(peek_node_arg(i));
      }
      d_work.erase(d_work.begin() + idx - 1, d_work.begin() + idx + 1);
      d_work_control.pop_back();
    }
    else if (token == Token::REAL_DIV)
    {
      close_term_scope();
    }
    else
    {
      close_term_scope(peek_is_term_arg() ? pop_term_arg() : bitwuzla::Term());
    }
  }

  return res;
}

bool
Parser::close_term_as(ParsedItem& item)
{
  if (nargs() != 1)
  {
    return error("expected exactly 1 term argument to 'as', got "
                     + std::to_string(nargs() > 0 ? nargs() - 1 : 0),
                 item.d_coo);
  }
  assert(std::holds_alternative<bitwuzla::Sort>(item.d_item));
  assert(std::get<bitwuzla::Sort>(item.d_item).is_array());
  set_item(item_open(),
           Token::TERM,
           bitwuzla::mk_const_array(std::get<bitwuzla::Sort>(item.d_item),
                                    pop_term_arg()));
  return true;
}

bool
Parser::close_term_bang(ParsedItem& item)
{
  size_t n = nargs();
  if (n < 3)
  {
    return error(
        "invalid annotation syntax, expected at least 3 arguments, got "
            + std::to_string(n),
        item.d_coo);
  }

  size_t size = d_work.size();

  // term
  size_t term_idx = size - n;
  if (!peek_is_term_arg(term_idx))
  {
    return error("invalid annotation syntax, expected term",
                 d_work[term_idx].d_coo);
  }
  bitwuzla::Term term = peek_term_arg(term_idx);

  // attributes
  size_t idx = size - n + 1;
  while (idx < size)
  {
    if (!peek_is_node_arg(idx))
    {
      return error("invalid annotation syntax, expected attribute",
                   d_work[idx].d_coo);
    }
    SymbolTable::Node* attribute = peek_node_arg(idx);
    if (attribute->d_token != Token::NAMED
        && attribute->d_token != Token::ATTRIBUTE)
    {
      return error("invalid annotation syntax, expected attribute",
                   d_work[idx].d_coo);
    }
    idx += 1;

    // we only support :named at the moment
    if (attribute->d_token == Token::NAMED)
    {
      if (!peek_is_node_arg(idx))
      {
        return error("invalid annotation syntax, expected symbol",
                     d_work[idx].d_coo);
      }
      SymbolTable::Node* symbol = peek_node_arg(idx++);
      symbol->d_term            = term;
      set_item(item, Token::TERM, symbol->d_term);
      if (d_record_named_assertions)
      {
        d_named_assertions[symbol->d_term] = symbol;
      }
    }
    // all other attributes are ignored
    else
    {
      idx += 1;  // ignore attribute value
      set_item(item, Token::TERM, term);
      Msg(1) << "warning: unsupported annotation attribute '"
             << attribute->d_symbol << "'";
    }
  }
  d_skip_attribute_value = false;
  d_work.resize(size - n);
  return true;
}

bool
Parser::close_term_array(ParsedItem& item)
{
  Token token = item.d_token;
  std::vector<bitwuzla::Term> args;
  if (token == Token::ARRAY_SELECT)
  {
    if (!pop_args(item, args))
    {
      return false;
    }
    set_item(
        item,
        Token::TERM,
        bitwuzla::mk_term(bitwuzla::Kind::ARRAY_SELECT, {args[0], args[1]}));
    return true;
  }

  assert(item.d_token == Token::ARRAY_STORE);
  if (!pop_args(item, args))
  {
    return false;
  }
  set_item(
      item, Token::TERM, bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE, args));
  return true;
}

bool
Parser::close_term_core(ParsedItem& item)
{
  Token token = item.d_token;
  std::vector<bitwuzla::Term> args;
  bitwuzla::Kind kind = bitwuzla::Kind::VALUE;

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
  if (!pop_args(item, args))
  {
    return false;
  }
  set_item(item, Token::TERM, bitwuzla::mk_term(kind, args));
  return true;
}

bool
Parser::close_term_bv(ParsedItem& item)
{
  Token token = item.d_token;
  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> idxs;
  bitwuzla::Kind kind = bitwuzla::Kind::VALUE;

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
    case Token::BV_NEGO: kind = bitwuzla::Kind::BV_NEG_OVERFLOW; break;
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
    case Token::BV_DEC: kind = bitwuzla::Kind::BV_DEC; break;
    case Token::BV_INC: kind = bitwuzla::Kind::BV_INC; break;
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
  if (!pop_args(item, args))
  {
    return false;
  }
  assert(args.size());
  set_item(item, Token::TERM, bitwuzla::mk_term(kind, args, item.d_uints));
  return true;
}

bool
Parser::close_term_fp(ParsedItem& item)
{
  Token token = item.d_token;
  std::vector<bitwuzla::Term> args;
  bitwuzla::Kind kind = bitwuzla::Kind::VALUE;

  if (token == Token::FP_TO_FP || token == Token::FP_TO_FP_UNSIGNED)
  {
    if (!pop_args(item, args))
    {
      return false;
    }
    if (!item.d_strs.empty())
    {
      assert(args.size() == 1);
      if (item.d_strs.size() == 1)
      {
        set_item(item,
                 Token::TERM,
                 bitwuzla::mk_fp_value(
                     bitwuzla::mk_fp_sort(item.d_uints[0], item.d_uints[1]),
                     args[0],
                     item.d_strs[0]));
      }
      else
      {
        assert(item.d_strs.size() == 2);
        set_item(item,
                 Token::TERM,
                 bitwuzla::mk_fp_value(
                     bitwuzla::mk_fp_sort(item.d_uints[0], item.d_uints[1]),
                     args[0],
                     item.d_strs[0],
                     item.d_strs[1]));
      }
      return true;
    }
    if (args.size() == 1)
    {
      assert(item.d_uints.size() == 2);
      assert(item.d_strs.empty());
      set_item(item,
               Token::TERM,
               bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_FP_FROM_BV, args, item.d_uints));
      return true;
    }
    assert(args.size() == 2);
    set_item(item,
             Token::TERM,
             bitwuzla::mk_term(args[1].sort().is_bv()
                                   ? (token == Token::FP_TO_FP_UNSIGNED
                                          ? bitwuzla::Kind::FP_TO_FP_FROM_UBV
                                          : bitwuzla::Kind::FP_TO_FP_FROM_SBV)
                                   : bitwuzla::Kind::FP_TO_FP_FROM_FP,
                               {args[0], args[1]},
                               item.d_uints));
    return true;
  }

  if (token == Token::REAL_DIV)
  {
    if (item.d_strs.size() != 2)
    {
      return error("expected 2 arguments to '" + std::to_string(item.d_token)
                       + "', got " + std::to_string(nargs()),
                   item.d_coo);
    }
    ParsedItem& prev = item_prev();
    prev.d_strs.insert(
        prev.d_strs.end(), item.d_strs.begin(), item.d_strs.end());
    prev.d_from_rational = true;
    assert(d_work.back().d_token == Token::REAL_DIV);
    d_work.pop_back();
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
  if (!pop_args(item, args))
  {
    return false;
  }
  assert(args.size());
  if (token == Token::FP_FP && args[0].is_value() && args[1].is_value()
      && args[2].is_value())
  {
    set_item(
        item, Token::TERM, bitwuzla::mk_fp_value(args[0], args[1], args[2]));
    return true;
  }
  set_item(item, Token::TERM, bitwuzla::mk_term(kind, args, item.d_uints));
  return true;
}

bool
Parser::close_term_fun_app(ParsedItem& item)
{
  assert(nargs() > 0);

  std::vector<bitwuzla::Term> args;
  if (!pop_args(item, args))
  {
    return false;
  }
  set_item(item, Token::TERM, bitwuzla::mk_term(bitwuzla::Kind::APPLY, args));
  return true;
}

bool
Parser::close_term_let(ParsedItem& item)
{
  if (nargs() == 0 || !peek_is_term_arg())
  {
    return error_arg("expected (single) term as argument to '"
                     + std::to_string(item.d_token) + "'");
  }
  set_item(item, Token::TERM, pop_term_arg());
  size_t idx = idx_open();
  size_t n   = nargs();
  for (size_t i = 0; i < n; ++i)
  {
    SymbolTable::Node* symbol = peek_node_arg(idx + 1 + i);
    assert(symbol);
    assert(symbol->d_token == Token::SYMBOL);
    assert(symbol->d_coo.line);
    assert(!symbol->d_term.is_null());
    d_table.remove(symbol);
  }
  d_work.resize(d_work.size() - n);
  return true;
}

bool
Parser::close_term_letbind(ParsedItem& item)
{
  if (nargs() != 2)
  {
    return error("expected 2 arguments to variable binding, got "
                     + std::to_string(nargs()),
                 item.d_coo);
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
Parser::close_term_parletbind(ParsedItem& item)
{
  (void) item;
  assert(d_is_var_binding);
  d_is_var_binding = false;
  assert(!d_expect_body);
  d_expect_body = true;
  return true;
}

bool
Parser::close_term_quant(ParsedItem& item)
{
  assert(item.d_token == Token::FORALL || item.d_token == Token::EXISTS);
  std::vector<bitwuzla::Term> args;
  if (!pop_args(item, args))
  {
    return false;
  }
  set_item(
      item,
      Token::TERM,
      bitwuzla::mk_term(item.d_token == Token::FORALL ? bitwuzla::Kind::FORALL
                                                      : bitwuzla::Kind::EXISTS,
                        args));
  return true;
}

bool
Parser::close_term_sorted_var(ParsedItem& item)
{
  if (nargs() != 1)
  {
    return error("expected one single variable at sorted variable expression",
                 item.d_coo);
  }
  assert(peek_is_term_arg());
  assert(peek_term_arg().is_variable());
  assert(!d_is_sorted_var);
  d_is_sorted_var = true;
  assert(peek_item_is_token(Token::SORTED_VAR, idx_open()));
  d_work.erase(d_work.begin() + idx_open());
  return true;
}

bool
Parser::close_term_sorted_vars(ParsedItem& item)
{
  (void) item;
  assert(d_is_sorted_var);
  d_is_sorted_var = false;
  assert(!d_expect_body);
  d_expect_body = true;
  assert(peek_item_is_token(Token::SORTED_VARS, idx_open()));
  d_work.erase(d_work.begin() + idx_open());
  return true;
}

/* -------------------------------------------------------------------------- */

bool
Parser::parse_sort(bitwuzla::Sort& sort, bool look_ahead, Token la)
{
  Token token = look_ahead ? la : next_token();
  if (!check_token(token))
  {
    return false;
  }

  if (token == Token::BOOL)
  {
    sort = bitwuzla::mk_bool_sort();
  }
  else if (token == Token::FP_FLOAT16)
  {
    sort = bitwuzla::mk_fp_sort(5, 11);
  }
  else if (token == Token::FP_FLOAT32)
  {
    sort = bitwuzla::mk_fp_sort(8, 24);
  }
  else if (token == Token::FP_FLOAT64)
  {
    sort = bitwuzla::mk_fp_sort(11, 53);
  }
  else if (token == Token::FP_FLOAT128)
  {
    sort = bitwuzla::mk_fp_sort(15, 113);
  }
  else if (token == Token::FP_ROUNDINGMODE)
  {
    sort = bitwuzla::mk_rm_sort();
  }
  else if (token == Token::LPAR)
  {
    token = next_token();
    if (!check_token(token))
    {
      return false;
    }
    if (token == Token::ARRAY)
    {
      return parse_sort_array(sort);
    }
    if (token == Token::AS)
    {
      return parse_open_term_as();
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
    return parse_sort_bv_fp(sort);
  }
  else if (token == Token::SYMBOL)
  {
    assert(d_lexer->has_token());
    std::string symbol      = d_lexer->token();
    SymbolTable::Node* node = d_table.find(symbol);
    if (!node || node->d_sort.is_null())
    {
      return error("invalid sort '" + symbol + "'");
    }
    sort = node->d_sort;
  }
  else
  {
    return error("expected '(' or sort keyword");
  }
  return true;
}

bool
Parser::parse_sort_array(bitwuzla::Sort& sort)
{
  bitwuzla::Sort index, element;
  if (!parse_sort(index))
  {
    return false;
  }
  if (!parse_sort(element))
  {
    return false;
  }
  if (!parse_rpar())
  {
    return false;
  }
  sort = bitwuzla::mk_array_sort(index, element);
  return true;
}

bool
Parser::parse_sort_bv_fp(bitwuzla::Sort& sort)
{
  Token token = next_token();
  if (!check_token(token))
  {
    return false;
  }

  if (token == Token::BV_BITVEC)
  {
    uint64_t size;
    if (!parse_uint64(size))
    {
      return false;
    }
    if (size == 0)
    {
      return error("invalid bit-vector size '0'");
    }
    if (!parse_rpar())
    {
      return false;
    }
    sort = bitwuzla::mk_bv_sort(size);
    return true;
  }
  if (token == Token::FP_FLOATINGPOINT)
  {
    uint64_t esize = 0;
    if (!parse_uint64(esize))
    {
      return false;
    }
    if (esize < 2)
    {
      return error("invalid exponent size '" + std::to_string(esize)
                   + "', must be > 1");
    }
    uint64_t ssize = 0;
    if (!parse_uint64(ssize))
    {
      return false;
    }
    if (ssize < 2)
    {
      return error("invalid significand size '" + std::to_string(ssize)
                   + "', must be > 1");
    }
    if (!parse_rpar())
    {
      return false;
    }
    sort = bitwuzla::mk_fp_sort(esize, ssize);
    return true;
  }
  return error("expected '" + std::to_string(Token::BV_BITVEC) + "' or '"
               + std::to_string(Token::FP_FLOATINGPOINT) + "'");
}

/* -------------------------------------------------------------------------- */

void
Parser::open_term_scope()
{
  push_item(Token::LPAR, d_lexer->coo());
  d_work_control.push_back(d_work.size());
  push_item(Token::OPEN, d_lexer->coo());
}

void
Parser::close_term_scope(const std::optional<bitwuzla::Term>& term)
{
  assert(d_work.size());
  assert(d_work.back().d_token == Token::LPAR);
  if (term)
  {
    ParsedItem& cur = d_work.back();
    set_item(cur, Token::TERM, *term);
  }
  else
  {
    d_work.pop_back();
  }
  d_work_control.pop_back();
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
Parser::error(const std::string& error_msg,
              const std::optional<Lexer::Coordinate>& coo)
{
  assert(d_lexer);
  const Lexer::Coordinate& c = coo ? *coo : d_lexer->coo();
  d_error = d_infile_name + ":" + std::to_string(c.line) + ":"
            + std::to_string(c.col) + ": " + error_msg;
  //#ifndef NDEBUG
  //  std::cout << "[error] " << d_error << std::endl;
  //  assert(false);
  //#endif
  return false;
}

bool
Parser::error_arg(const std::string& error_msg)
{
  assert(!d_work.empty());
  return error(error_msg, d_work.back().d_coo);
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

const Lexer::Coordinate&
Parser::arg_coo(size_t idx) const
{
  assert(idx < d_work.size());
  return d_work[idx].d_coo;
}

bitwuzla::Term
Parser::pop_term_arg()
{
  assert(peek_is_term_arg());
  bitwuzla::Term res = std::get<bitwuzla::Term>(d_work.back().d_item);
  d_work.pop_back();
  return res;
}

SymbolTable::Node*
Parser::pop_node_arg(bool set_coo)
{
  assert(peek_is_node_arg());
  SymbolTable::Node* res = std::get<SymbolTable::Node*>(d_work.back().d_item);
  if (set_coo)
  {
    res->d_coo = d_work.back().d_coo;
  }
  d_work.pop_back();
  return res;
}

bool
Parser::pop_args(const ParsedItem& item, std::vector<bitwuzla::Term>& args)
{
  Token token     = item.d_token;
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
    case Token::BV_NEGO:
    case Token::BV_NOT:
    case Token::BV_DEC:
    case Token::BV_INC:
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
    case Token::FP_NOTANUMBER:
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
  size_t cnt_args = nargs();
  if (n_args > 0)
  {
    if (cnt_args != n_args)
    {
      return error("expected " + std::to_string(n_args) + " argument"
                       + (n_args > 1 ? "s" : "") + " to '"
                       + std::to_string(token) + "', got "
                       + std::to_string(cnt_args),
                   item.d_coo);
    }
  }
  else if (token == Token::FP_TO_FP)
  {
    size_t n_strs = item.d_strs.size();
    if (n_strs)
    {
      if (cnt_args != 1 || (!item.d_from_rational && n_strs != 1)
          || (item.d_from_rational && n_strs != 2))
      {
        return error(
            "expected 2 arguments to '" + std::to_string(token) + "', got "
                + std::to_string(
                    cnt_args + (item.d_from_rational ? n_strs - 1 : n_strs)),
            item.d_coo);
      }
    }
    else if (cnt_args != 1 && cnt_args != 2)
    {
      return error("expected 1 or 2 arguments to '" + std::to_string(token)
                       + "', got " + std::to_string(cnt_args),
                   item.d_coo);
    }
  }
  else if (token == Token::FP_TO_FP_UNSIGNED)
  {
    if (cnt_args != 2)
    {
      return error("expected 2 arguments to '" + std::to_string(token)
                       + "', got " + std::to_string(cnt_args - 2),
                   item.d_coo);
    }
  }
  else if (cnt_args < 2)
  {
    return error("expected at least 2 arguments to '" + std::to_string(token)
                     + "', got " + std::to_string(cnt_args),
                 item.d_coo);
  }

  // check number of indices
  if (item.d_uints.size() < n_idxs)
  {
    return error("expected " + std::to_string(n_idxs) + " "
                     + (n_idxs > 1 ? "indices" : "index") + " as argument to '"
                     + std::to_string(token) + "', got "
                     + std::to_string(item.d_uints.size()),
                 item.d_coo);
  }

  // actual number of arguments
  n_args = cnt_args;

  // check arguments and indices and pop
  size_t idx = idx_open() + 1;  // start index of args
  assert(idx < d_work.size());
  assert(args.empty());
  args.resize(n_args);

  for (size_t i = idx, n = idx + n_args; i < n; ++i)
  {
    if (!peek_is_term_arg(i))
    {
      return error("expected term", d_work[i].d_coo);
    }
  }

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
    case Token::BV_NEGO:
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
    case Token::BV_DEC:
    case Token::BV_INC:
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
      if (!args[1].sort().is_bv() || args[1].sort().bv_size() <= 1)
      {
        return error(
            "expected bit-vector term of size > 1 at index 1 as argument to '"
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
    case Token::FP_NOTANUMBER:
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
      if (item.d_strs.empty() && n_args == 1)
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
      // ((_ to_fp eb sb) RoundingMode (_ FloatingPoint eb sb))
      // ((_ to_fp eb sb) RoundingMode (_ BitVec m))
      // ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m))
      if (cnt_args == 2)
      {
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
                     item.d_coo);
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
                             + " as argument to '" + std::to_string(token)
                             + "'",
                         arg_coo(j));
          }
          if (args[i].sort().is_array())
          {
            return error("variable of array sort not supported", arg_coo(j));
          }
          if (args[i].sort().is_fun())
          {
            return error("variable of function sort not supported", arg_coo(j));
          }
          // remove sorted variables from symbol table
          d_table.remove(args[i].str());
        }
        else
        {
          if (!args[i].sort().is_bool())
          {
            return error("expected Boolean term as body to '"
                             + std::to_string(token) + "'",
                         arg_coo(j));
          }
        }
      }
    }
    break;

    default: assert(false);
  }

  // check indices
  if (token == Token::BV_EXTRACT)
  {
    if (item.d_uints[0] >= args[0].sort().bv_size())
    {
      return error("upper index '" + std::to_string(item.d_uints[0])
                       + "' too high for bit-vector of size "
                       + std::to_string(args[0].sort().bv_size())
                       + " as argument to '" + std::to_string(token) + "'",
                   item.d_uints_coo[0]);
    }
    if (item.d_uints[0] < item.d_uints[1])
    {
      return error("upper index must be >= lower index as argument to '"
                       + std::to_string(token) + "'",
                   item.d_uints_coo[0]);
    }
  }
  else if (token == Token::BV_REPEAT)
  {
    if (((uint64_t) (UINT64_MAX / item.d_uints[0])) < args[0].sort().bv_size())
    {
      return error(
          "index '" + std::to_string(item.d_uints[0]) + "' as argument to '"
              + std::to_string(token)
              + "' too large, resulting bit-vector size exceeds maximum "
              + "bit-vector size of " + std::to_string(UINT64_MAX),
          item.d_uints_coo[0]);
    }
  }
  else if (token == Token::BV_SIGN_EXTEND || token == Token::BV_ZERO_EXTEND)
  {
    if (item.d_uints[0] > UINT64_MAX - args[0].sort().bv_size())
    {
      return error(
          "index '" + std::to_string(item.d_uints[0]) + "' as argument to '"
              + std::to_string(token)
              + "' too large, resulting bit-vector size exceeds maximum "
              + "bit-vector size of " + std::to_string(UINT64_MAX),
          item.d_uints_coo[0]);
    }
  }
  else if (token == Token::FP_TO_FP && args[0].sort().is_bv())
  {
    if (args[0].sort().bv_size() != item.d_uints[0] + item.d_uints[1])
    {
      return error("size of bit-vector term '"
                   + std::to_string(args[0].sort().bv_size())
                   + " does not match floating-point format '"
                   + std::to_string(item.d_uints[0]) + " "
                   + std::to_string(item.d_uints[1]) + "'");
    }
  }

  d_work.resize(d_work.size() - n_args);
  return true;
}

#ifndef NDEBUG
void
Parser::print_work_stack()
{
  std::cout << "work stack:" << std::endl;
  std::cout << "-----------" << std::endl;
  for (auto& w : d_work)
  {
    std::cout << "  " << w.d_token;
    if (std::holds_alternative<bitwuzla::Term>(w.d_item))
    {
      std::cout << ": bitwuzla::Term: " << std::get<bitwuzla::Term>(w.d_item)
                << std::endl;
    }
    else if (std::holds_alternative<bitwuzla::Sort>(w.d_item))
    {
      std::cout << ": bitwuzla::Sort: " << std::get<bitwuzla::Sort>(w.d_item)
                << std::endl;
    }
    else if (std::holds_alternative<SymbolTable::Node*>(w.d_item))
    {
      SymbolTable::Node* node = std::get<SymbolTable::Node*>(w.d_item);
      if (node)
      {
        std::cout << ": SymbolTable::Node*: "
                  << (node ? node->d_symbol : "(nil)");
      }
      std::cout << std::endl;
    }
    else
    {
      std::cout << "unsupported item" << std::endl;
    }
    if (w.d_uints.size())
    {
      std::cout << "    d_uints: {";
      for (uint64_t u : w.d_uints)
      {
        std::cout << " " << u;
      }
      std::cout << " }" << std::endl;
    }
    if (w.d_strs.size())
    {
      std::cout << "    d_strs: {";
      for (auto& s : w.d_strs)
      {
        std::cout << " " << s;
      }
      std::cout << " }" << std::endl;
    }
  }
}

void
Parser::print_work_control_stack()
{
  std::cout << "work control stack: {";
  for (auto& w : d_work_control)
  {
    std::cout << " " << w;
  }
  std::cout << " }" << std::endl;
}
#endif

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

/* -------------------------------------------------------------------------- */
}  // namespace parser::smt2
}  // namespace bzla
