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

#include "bv/bitvector.h"

namespace bzla {
namespace parser::btor2 {

/* Parser public ------------------------------------------------------------ */

Parser::Parser(bitwuzla::TermManager& tm,
               bitwuzla::Options& options,
               std::ostream* out)
    : bzla::parser::Parser(tm, options, out)
{
  if (d_error.empty())
  {
    d_lexer.reset(new Lexer());
  }
  init_bitwuzla();
  bitwuzla::Sort bv1 = d_tm.mk_bv_sort(1);
  d_bv1_one          = d_tm.mk_bv_one(bv1);
  d_bv1_zero         = d_tm.mk_bv_zero(bv1);
}

Parser::~Parser() {}

void
Parser::reset()
{
  d_done = false;
}

bool
Parser::parse(const std::string& input, bool parse_only, bool parse_file)
{
  reset();

  std::istream* instream = &std::cin;
  std::ifstream infile;
  std::stringstream instring;

  if (parse_file)
  {
    if (input != "<stdin>")
    {
      infile.open(input, std::ifstream::in);
      if (!infile)
      {
        d_error = "failed to open '" + input + "'";
        return false;
      }
      instream = &infile;
    }
  }
  else
  {
    instring << input;
    instream = &instring;
  }

  bool res = parse(parse_file ? input : "<string>", *instream, parse_only);
  if (infile.is_open())
  {
    infile.close();
  }
  return res;
}

bool
Parser::parse(const std::string& infile_name,
              std::istream& input,
              bool parse_only)
{
  d_parse_only = parse_only;

  util::Timer timer(d_statistics.time_parse);
  Log(2) << "parse " << d_infile_name;

  d_infile_name = infile_name;
  d_lexer->init(&input);

  if (!d_error.empty())
  {
    d_error = "parser in unsafe state after parse error";
    return false;
  }

  while (parse_line() && !d_done && !terminate())
    ;

  Msg(1) << "parsed " << d_statistics.num_lines << " lines in "
         << ((double) d_statistics.time_parse.elapsed() / 1000) << " seconds";

  if (d_error.empty())
  {
    if (!d_parse_only)
    {
      if (d_bad_properties.empty())
      {
        // If no safety properties checked, do one check-sat call.
        bitwuzla::Result res = d_bitwuzla->check_sat();
        std::cout << res << std::endl;
        if (d_auto_print_model && res == bitwuzla::Result::SAT)
        {
          if (!print_model())
          {
            return false;
          }
        }
      }
      else
      {
        for (const auto& [bad, id, symbol] : d_bad_properties)
        {
          d_bitwuzla->push(1);
          d_bitwuzla->assert_formula(bad);
          auto res = d_bitwuzla->check_sat();
          (*d_out) << "Bad property " << id;
          if (!symbol.empty())
          {
            (*d_out) << " (" << symbol << ")";
          }
          if (res == bitwuzla::Result::SAT)
          {
            (*d_out) << " satisfiable." << std::endl;
            if (d_auto_print_model)
            {
              if (!print_model())
              {
                return false;
              }
            }
          }
          else if (res == bitwuzla::Result::UNSAT)
          {
            (*d_out) << " unsatisfiable." << std::endl;
          }
          d_bitwuzla->pop(1);
        }
        d_bad_properties.clear();
      }
    }
    return true;
  }
  return false;
}

bool
Parser::parse_term(const std::string& input, bitwuzla::Term& res)
{
  std::stringstream instring;
  instring << input;
  reset();
  d_infile_name = "<string>";
  d_lexer->init(&instring);
  ParsedKind kind;
  int64_t line_id = 0;
  if (!parse_line(&kind, &line_id))
  {
    return false;
  }
  assert(line_id);
  if (kind != ParsedKind::TERM)
  {
    d_error = "expected string that represents term";
    return false;
  }
  res = d_term_map.at(line_id);
  assert(!res.is_null());
  return true;
}

bool
Parser::parse_sort(const std::string& input, bitwuzla::Sort& res)
{
  std::stringstream instring;
  instring << input;
  reset();
  d_infile_name = "<string>";
  d_lexer->init(&instring);

  ParsedKind kind;
  int64_t line_id = 0;
  if (!parse_line(&kind, &line_id))
  {
    return false;
  }
  assert(line_id);
  if (kind != ParsedKind::SORT)
  {
    d_error = "expected string that represents sort declaration";
    return false;
  }
  res = d_sort_map.at(line_id);
  assert(!res.is_null());
  return true;
}

bool
Parser::print_model()
{
  if (!d_options.get(bitwuzla::Option::PRODUCE_MODELS))
  {
    d_error = "model generation is not enabled";
    return false;
  }

  std::stringstream ss;
  for (const auto& [id, input] : d_inputs)
  {
    auto value  = d_bitwuzla->get_value(input);
    auto symbol = input.symbol();
    if (input.sort().is_bv())
    {
      ss << id << " " << value.value<std::string>(2);
      if (symbol)
      {
        ss << " " << symbol->get();
      }
      ss << std::endl;
    }
    else if (input.sort().is_array())
    {
      bitwuzla::Term cur = value;
      while (cur.kind() == bitwuzla::Kind::ARRAY_STORE)
      {
        auto index   = d_bitwuzla->get_value(cur[1]);
        auto element = d_bitwuzla->get_value(cur[2]);
        ss << id << "[" << index.value<std::string>(2) << "]";
        ss << " " << element.value<std::string>(2);
        cur = cur[0];
        if (symbol)
        {
          ss << " " << symbol->get();
        }
        ss << std::endl;
      }
      if (cur.kind() == bitwuzla::Kind::CONST_ARRAY)
      {
        ss << id << "[*]";
        ss << " " << cur[0].value<std::string>(2);
        if (symbol)
        {
          ss << " " << symbol->get();
        }
        ss << std::endl;
      }
    }
  }
  (*d_out) << ss.str();
  d_out->flush();
  return true;
}

std::vector<bitwuzla::Sort>
Parser::get_declared_sorts() const
{
  return {};
}

std::vector<bitwuzla::Term>
Parser::get_declared_funs() const
{
  std::vector<bitwuzla::Term> res;
  for (const auto& [id, term] : d_term_map)
  {
    if (term.symbol())
    {
      res.push_back(term);
    }
  }
  return res;
}

/* Parser private ----------------------------------------------------------- */

bitwuzla::Term
Parser::bool_term_to_bv1(const bitwuzla::Term& term) const
{
  if (!term.sort().is_bool()) return term;
  return d_tm.mk_term(bitwuzla::Kind::ITE, {term, d_bv1_one, d_bv1_zero});
}

bitwuzla::Term
Parser::bv1_term_to_bool(const bitwuzla::Term& term) const
{
  if (!term.sort().is_bv() || term.sort().bv_size() != 1)
  {
    return term;
  }
  return d_tm.mk_term(bitwuzla::Kind::EQUAL, {term, d_bv1_one});
}

bool
Parser::parse_line(ParsedKind* pkind, int64_t* id)
{
  Token token = d_lexer->next_token(Token::NUMBER_DEC);

  if (token == Token::ENDOFFILE)
  {
    d_done = true;
    return true;
  }

  if (token == Token::INVALID)
  {
    return error_invalid();
  }

  int64_t line_id = 0;
  if (!parse_number(false, line_id, true, token))
  {
    return false;
  }
  if (line_id > INT32_MAX)
  {
    return error("line id '" + std::to_string(line_id) + "' exceeds INT32_MAX");
  }

  assert(line_id);
  if (id)
  {
    *id = line_id;
  }

  Token op = d_lexer->next_token();
  if (!check_token(op))
  {
    return false;
  }

  if (op == Token::SORT)
  {
    if (pkind)
    {
      *pkind = ParsedKind::SORT;
    }
    return parse_sort(line_id);
  }

  bitwuzla::Term term;
  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> idxs;
  bitwuzla::Kind kind = bitwuzla::Kind::CONSTANT;

  if (pkind)
  {
    *pkind = ParsedKind::TERM;
  }

  switch (op)
  {
    case Token::CONST:
    case Token::CONSTH:
    case Token::CONSTD:
    case Token::ONE:
    case Token::ONES:
    case Token::ZERO:
    case Token::INPUT: break;

    case Token::CONSTRAINT:
      if (!parse_term(term))
      {
        return false;
      }
      d_bitwuzla->assert_formula(bv1_term_to_bool(term));
      if (pkind)
      {
        *pkind = ParsedKind::CONSTRAINT;
      }
      // Symbol not used
      parse_opt_symbol();
      return true;

    case Token::EQ:
    case Token::IFF: kind = bitwuzla::Kind::EQUAL; break;

    case Token::ADD: kind = bitwuzla::Kind::BV_ADD; break;
    case Token::AND: kind = bitwuzla::Kind::BV_AND; break;
    case Token::CONCAT: kind = bitwuzla::Kind::BV_CONCAT; break;
    case Token::DEC: kind = bitwuzla::Kind::BV_DEC; break;
    case Token::IMPLIES: kind = bitwuzla::Kind::IMPLIES; break;
    case Token::INC: kind = bitwuzla::Kind::BV_INC; break;
    case Token::ITE: kind = bitwuzla::Kind::ITE; break;
    case Token::MUL: kind = bitwuzla::Kind::BV_MUL; break;
    case Token::NAND: kind = bitwuzla::Kind::BV_NAND; break;
    case Token::NEQ: kind = bitwuzla::Kind::DISTINCT; break;
    case Token::NEG: kind = bitwuzla::Kind::BV_NEG; break;
    case Token::NEGO: kind = bitwuzla::Kind::BV_NEG_OVERFLOW; break;
    case Token::NOR: kind = bitwuzla::Kind::BV_NOR; break;
    case Token::NOT: kind = bitwuzla::Kind::BV_NOT; break;
    case Token::OR: kind = bitwuzla::Kind::BV_OR; break;
    case Token::READ: kind = bitwuzla::Kind::ARRAY_SELECT; break;
    case Token::REDAND: kind = bitwuzla::Kind::BV_REDAND; break;
    case Token::REDOR: kind = bitwuzla::Kind::BV_REDOR; break;
    case Token::REDXOR: kind = bitwuzla::Kind::BV_REDXOR; break;
    case Token::ROL: kind = bitwuzla::Kind::BV_ROL; break;
    case Token::ROR: kind = bitwuzla::Kind::BV_ROR; break;
    case Token::SADDO: kind = bitwuzla::Kind::BV_SADD_OVERFLOW; break;
    case Token::SDIV: kind = bitwuzla::Kind::BV_SDIV; break;
    case Token::SDIVO: kind = bitwuzla::Kind::BV_SDIV_OVERFLOW; break;
    case Token::SEXT: kind = bitwuzla::Kind::BV_SIGN_EXTEND; break;
    case Token::SGT: kind = bitwuzla::Kind::BV_SGT; break;
    case Token::SGTE: kind = bitwuzla::Kind::BV_SGE; break;
    case Token::SLICE: kind = bitwuzla::Kind::BV_EXTRACT; break;
    case Token::SLL: kind = bitwuzla::Kind::BV_SHL; break;
    case Token::SLT: kind = bitwuzla::Kind::BV_SLT; break;
    case Token::SLTE: kind = bitwuzla::Kind::BV_SLE; break;
    case Token::SMOD: kind = bitwuzla::Kind::BV_SMOD; break;
    case Token::SMULO: kind = bitwuzla::Kind::BV_SMUL_OVERFLOW; break;
    case Token::SRA: kind = bitwuzla::Kind::BV_ASHR; break;
    case Token::SREM: kind = bitwuzla::Kind::BV_SREM; break;
    case Token::SRL: kind = bitwuzla::Kind::BV_SHR; break;
    case Token::SSUBO: kind = bitwuzla::Kind::BV_SSUB_OVERFLOW; break;
    case Token::SUB: kind = bitwuzla::Kind::BV_SUB; break;
    case Token::UADDO: kind = bitwuzla::Kind::BV_UADD_OVERFLOW; break;
    case Token::UDIV: kind = bitwuzla::Kind::BV_UDIV; break;
    case Token::UEXT: kind = bitwuzla::Kind::BV_ZERO_EXTEND; break;
    case Token::UGT: kind = bitwuzla::Kind::BV_UGT; break;
    case Token::UGTE: kind = bitwuzla::Kind::BV_UGE; break;
    case Token::ULT: kind = bitwuzla::Kind::BV_ULT; break;
    case Token::ULTE: kind = bitwuzla::Kind::BV_ULE; break;
    case Token::UMULO: kind = bitwuzla::Kind::BV_UMUL_OVERFLOW; break;
    case Token::UREM: kind = bitwuzla::Kind::BV_UREM; break;
    case Token::USUBO: kind = bitwuzla::Kind::BV_USUB_OVERFLOW; break;
    case Token::WRITE: kind = bitwuzla::Kind::ARRAY_STORE; break;
    case Token::XNOR: kind = bitwuzla::Kind::BV_XNOR; break;
    case Token::XOR: kind = bitwuzla::Kind::BV_XOR; break;

    case Token::BAD: {
      if (!parse_term(term))
      {
        return false;
      }
      const char* symbol = parse_opt_symbol();
      if (pkind)
      {
        *pkind = ParsedKind::CONSTRAINT;
      }
      d_bad_properties.emplace_back(
          bv1_term_to_bool(term), line_id, symbol ? symbol : "");
      return true;
    }

    case Token::FAIR:
    case Token::INIT:
    case Token::JUSTICE:
    case Token::NEXT:
    case Token::OUTPUT:
    case Token::STATE:
      return error("unsupported operator '" + std::to_string(op)
                   + "', model checking extensions not supported");

    default:
      return error("expected operator, got '" + std::string(d_lexer->token())
                   + "'");
  }

  int64_t sort_id = 0;
  if (!parse_number(false, sort_id))
  {
    return false;
  }
  auto it = d_sort_map.find(sort_id);
  if (it == d_sort_map.end())
  {
    return error("invalid sort id '" + std::to_string(sort_id) + "'");
  }
  bitwuzla::Sort sort = it->second;
  assert(!sort.is_null());
  Lexer::Coordinate sort_coo = d_lexer->coo();

  switch (op)
  {
    case Token::CONST:
    case Token::CONSTD:
    case Token::CONSTH: {
      uint8_t base = 0;
      if (op == Token::CONST)
      {
        base  = 2;
        token = d_lexer->next_token(Token::NUMBER_BIN);
      }
      else if (op == Token::CONSTD)
      {
        base  = 10;
        token = d_lexer->next_token(Token::NUMBER_DEC);
      }
      else
      {
        base  = 16;
        token = d_lexer->next_token(Token::NUMBER_HEX);
      }
      if (!check_token(op))
      {
        return false;
      }
      std::string val = d_lexer->token();
      if (!sort.is_bv())
      {
        return error("expected bit-vector sort", sort_coo);
      }
      if (!BitVector::fits_in_size(sort.bv_size(), val, base))
      {
        return error("'" + val + "' of base "
                     + std::to_string(static_cast<uint32_t>(base))
                     + "does not fit into bit-vector of size "
                     + std::to_string(sort.bv_size()));
      }
      term = d_tm.mk_bv_value(sort, val, base);
      break;
    }

    case Token::INPUT: {
      const char* symbol = parse_opt_symbol();
      if (symbol)
      {
        term = d_tm.mk_const(sort, symbol);
      }
      else
      {
        term = d_tm.mk_const(sort);
      }
      d_inputs.emplace_back(line_id, term);
    }
    break;

    case Token::ONE:
      if (!sort.is_bv())
      {
        return error("expected bit-vector sort", sort_coo);
      }
      term = d_tm.mk_bv_one(sort);
      break;

    case Token::ONES:
      if (!sort.is_bv())
      {
        return error("expected bit-vector sort", sort_coo);
      }
      term = d_tm.mk_bv_ones(sort);
      break;

    case Token::ZERO:
      if (!sort.is_bv())
      {
        return error("expected bit-vector sort", sort_coo);
      }
      term = d_tm.mk_bv_zero(sort);
      break;

    case Token::ADD:
    case Token::AND:
    case Token::CONCAT:
    case Token::MUL:
    case Token::NAND:
    case Token::NOR:
    case Token::OR:
    case Token::ROL:
    case Token::ROR:
    case Token::SADDO:
    case Token::SDIV:
    case Token::SDIVO:
    case Token::SGT:
    case Token::SGTE:
    case Token::SLL:
    case Token::SLT:
    case Token::SLTE:
    case Token::SMOD:
    case Token::SMULO:
    case Token::SRA:
    case Token::SREM:
    case Token::SRL:
    case Token::SSUBO:
    case Token::SUB:
    case Token::UADDO:
    case Token::UDIV:
    case Token::UGT:
    case Token::UGTE:
    case Token::ULT:
    case Token::ULTE:
    case Token::UMULO:
    case Token::UREM:
    case Token::USUBO:
    case Token::XNOR:
    case Token::XOR:
      for (size_t i = 0; i < 2; ++i)
      {
        if (!parse_term(term))
        {
          return false;
        }
        term = bool_term_to_bv1(term);
        if (!term.sort().is_bv())
        {
          return error("expected bit-vector term, got term '"
                       + std::string(d_lexer->token()) + "'");
        }
        if (i > 0 && op != Token::CONCAT && args[i - 1].sort() != term.sort())
        {
          return error("terms with mismatching sort");
        }
        args.push_back(term);
      }
      break;

    case Token::DEC:
    case Token::INC:
    case Token::NEG:
    case Token::NEGO:
    case Token::NOT:
    case Token::REDAND:
    case Token::REDOR:
    case Token::REDXOR:
      if (!parse_term(term))
      {
        return false;
      }
      term = bool_term_to_bv1(term);
      if (!term.sort().is_bv())
      {
        return error("expected bit-vector term, got term '"
                     + std::string(d_lexer->token()) + "'");
      }
      args.push_back(term);
      break;

    case Token::SEXT:
    case Token::SLICE:
    case Token::UEXT: {
      if (!parse_term(term))
      {
        return false;
      }
      term = bool_term_to_bv1(term);
      if (!term.sort().is_bv())
      {
        return error("expected bit-vector term, got term '"
                     + std::string(d_lexer->token()) + "'");
      }
      args.push_back(term);
      int64_t uint = 0;
      if (!parse_number(false, uint))
      {
        return false;
      }
      idxs.push_back(uint);
      if (op == Token::SEXT || op == Token::UEXT)
      {
        if (term.sort().bv_size() + idxs[0] != sort.bv_size())
        {
          return error("expected bit-vector term of size "
                       + std::to_string(sort.bv_size())
                       + ", got a bit-vector term of size "
                       + std::to_string(term.sort().bv_size() + idxs[0]));
        }
      }
      else if (op == Token::SLICE)
      {
        if (!parse_number(false, uint))
        {
          return false;
        }
        idxs.push_back(uint);
        if (idxs[0] < idxs[1])
        {
          return error("invalid indices for '" + std::to_string(op)
                       + "', expected first index to be >= second index");
        }
        if (idxs[0] - idxs[1] + 1 != sort.bv_size())
        {
          return error("term with id " + std::to_string(line_id)
                       + " has bit-vector size "
                       + std::to_string(idxs[0] - idxs[1] + 1)
                       + " but expected sort '" + std::to_string(sort_id)
                       + "' of size " + std::to_string(sort.bv_size()));
        }
      }
      break;
    }

    case Token::EQ:
    case Token::NEQ:
      for (size_t i = 0; i < 2; ++i)
      {
        if (!parse_term(term))
        {
          return false;
        }
        term = bv1_term_to_bool(term);
        if (i > 0 && args[i - 1].sort() != term.sort())
        {
          return error("terms with mismatching sort");
        }
        args.push_back(term);
      }
      break;

    case Token::IFF:
    case Token::IMPLIES:
      for (size_t i = 0; i < 2; ++i)
      {
        if (!parse_term(term))
        {
          return false;
        }
        term = bv1_term_to_bool(term);
        if (!term.sort().is_bool())
        {
          return error("expected bit-vector term of size 1, got term '"
                       + std::string(d_lexer->token()) + "'");
        }
        if (i > 0 && args[i - 1].sort() != term.sort())
        {
          return error("terms with mismatching sort");
        }
        args.push_back(term);
      }
      break;

    case Token::ITE:
      for (size_t i = 0; i < 3; ++i)
      {
        if (!parse_term(term))
        {
          return false;
        }
        term = bv1_term_to_bool(term);
        if (i == 0)
        {
          if (!term.sort().is_bool())
          {
            return error("expected bit-vector term of size 1, got term '"
                         + std::string(d_lexer->token()) + "'");
          }
        }
        else if (i > 1 && args[i - 1].sort() != term.sort())
        {
          return error("terms with mismatching sort");
        }
        args.push_back(term);
      }
      break;
    case Token::READ:
      if (!parse_term(term))
      {
        return false;
      }
      if (!term.sort().is_array())
      {
        return error("expected array term, got term '"
                     + std::string(d_lexer->token()) + "'");
      }
      args.push_back(term);
      if (!parse_term(term))
      {
        return false;
      }
      term = bool_term_to_bv1(term);
      if (!term.sort().is_bv())
      {
        return error("expected bit-vector term, got term '"
                     + std::string(d_lexer->token()) + "'");
      }
      args.push_back(term);
      break;

    case Token::WRITE:
      if (!parse_term(term))
      {
        return false;
      }
      if (!term.sort().is_array())
      {
        return error("expected array term, got term '"
                     + std::string(d_lexer->token()) + "'");
      }
      if (term.sort() != sort)
      {
        return error("expected array term of sort '" + std::to_string(sort_id)
                     + "'");
      }
      args.push_back(term);
      for (size_t i = 0; i < 2; ++i)
      {
        if (!parse_term(term))
        {
          return false;
        }
        term = bool_term_to_bv1(term);
        if (!term.sort().is_bv())
        {
          return error("expected bit-vector term, got term '"
                       + std::string(d_lexer->token()) + "'");
        }
        if (i == 0)
        {
          if (term.sort() != sort.array_index())
          {
            return error("index term does not match index sort of array");
          }
        }
        else
        {
          if (term.sort() != sort.array_element())
          {
            return error("element term does not match element sort of array");
          }
        }
        args.push_back(term);
      }
      break;
    default: assert(false);
  }

  if (kind != bitwuzla::Kind::CONSTANT)
  {
    term = d_tm.mk_term(kind, args, idxs);
  }
  assert(
      sort.is_null() || term.is_null() || term.sort() == sort
      || (sort.is_bv() && sort.bv_size() == 1 && term.sort().is_bool())
      || (sort.is_bool() && term.sort().is_bv() && term.sort().bv_size() == 1));
  if (!term.is_null())
  {
    auto [it, inserted] = d_term_map.emplace(line_id, term);
    if (!inserted)
    {
      return error("invalid term id '" + std::to_string(line_id)
                   + "', already defined");
    }
  }

  // Ignore optional symbol
  parse_opt_symbol();

  return true;
}

bool
Parser::parse_number(bool sign, int64_t& res, bool look_ahead, Token la)
{
  Token token;
  if (look_ahead)
  {
    token = la;
  }
  else
  {
    token = d_lexer->next_token(Token::NUMBER_DEC);
    if (!check_token(token))
    {
      return false;
    }
  }
  if (token != Token::NUMBER_DEC)
  {
    return error("expected integer, got '" + std::string(d_lexer->token())
                 + "'");
  }
  assert(d_lexer->has_token());
  try
  {
    res = std::stoll(d_lexer->token());
    if (!sign && res < 0)
    {
      return error("expected non-negative integer, got '"
                   + std::string(d_lexer->token()) + "'");
    }
    return true;
  }
  catch (...)
  {
    return error("invalid 64 bit integer '" + std::string(d_lexer->token())
                 + "'");
  }
  return error("expected 64 bit integer");
}

const char*
Parser::parse_opt_symbol()
{
  int32_t ch = d_lexer->look_ahead();
  if (ch != ';' && ch != '\n')
  {
    d_lexer->next_token();
    return d_lexer->token();
  }
  return nullptr;
}

bool
Parser::parse_sort(int64_t line_id)
{
  Token token = d_lexer->next_token();
  if (!check_token(token))
  {
    return false;
  }

  if (token != Token::BITVEC && token != Token::ARRAY)
  {
    assert(d_lexer->has_token());
    return error("unexpected token '" + std::string(d_lexer->token()) + "'");
  }

  bitwuzla::Sort sort;
  if (token == Token::BITVEC)
  {
    int64_t bw = 0;
    if (!parse_number(false, bw))
    {
      return false;
    }
    sort = d_tm.mk_bv_sort(bw);
  }
  else
  {
    int64_t sindex = 0;
    if (!parse_number(false, sindex))
    {
      return false;
    }
    auto it = d_sort_map.find(sindex);
    if (it == d_sort_map.end())
    {
      return error("invalid sort id '" + std::to_string(sindex) + "'");
    }
    bitwuzla::Sort sort_index = it->second;

    int64_t selem = 0;
    if (!parse_number(false, selem))
    {
      return false;
    }
    it = d_sort_map.find(selem);
    if (it == d_sort_map.end())
    {
      return error("invalid sort id '" + std::to_string(selem) + "'");
    }
    bitwuzla::Sort sort_elem = it->second;
    sort                     = d_tm.mk_array_sort(sort_index, sort_elem);
  }
  auto [it, inserted] = d_sort_map.emplace(line_id, sort);
  if (!inserted)
  {
    return error("invalid sort id '" + std::to_string(line_id)
                 + "', already defined");
  }
  return true;
}

bool
Parser::parse_term(bitwuzla::Term& res)
{
  int64_t term_id = 0;
  if (!parse_number(true, term_id))
  {
    return false;
  }
  bool inv = term_id < 0;
  term_id  = inv ? -term_id : term_id;
  auto it  = d_term_map.find(term_id);
  if (it == d_term_map.end())
  {
    return error("invalid term id '" + std::to_string(term_id) + "'");
  }
  if (inv)
  {
    if (it->second.sort().is_bool())
    {
      res = d_tm.mk_term(bitwuzla::Kind::NOT, {it->second});
    }
    else if (it->second.sort().is_bv())
    {
      res = d_tm.mk_term(bitwuzla::Kind::BV_NOT, {it->second});
    }
    else
    {
      return error("invalid negative id '-" + std::to_string(term_id)
                   + "' for term that is neither bit-vector nor boolean");
    }
  }
  else
  {
    res = it->second;
  }
  return true;
}

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

/* Parser::Statistics ------------------------------------------------------- */

Parser::Statistics::Statistics()
    : num_lines(d_stats.new_stat<uint64_t>("parser::btor2:num_lines")),
      time_parse(
          d_stats.new_stat<util::TimerStatistic>("parser::btor2::time_parse"))
{
}

/* -------------------------------------------------------------------------- */

}  // namespace parser::btor2
}  // namespace bzla
