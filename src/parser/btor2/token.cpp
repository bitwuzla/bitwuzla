/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/btor2/token.h"

namespace bzla {
namespace parser::btor2 {

std::ostream&
operator<<(std::ostream& out, Token token)
{
  out << std::to_string(token);
  return out;
}
}
}

namespace std {

std::string
to_string(bzla::parser::btor2::Token token)
{
  using namespace bzla::parser::btor2;
  switch (token)
  {
    case Token::INVALID: return "<invalid token>";
    case Token::ENDOFFILE: return "<eof token>";
    case Token::NUMBER: return "<number token>";
    case Token::SYMBOL: return "<symbol token>";
    case Token::ADD: return "add";
    case Token::AND: return "and";
    case Token::ARRAY: return "array";
    case Token::BAD: return "bad";
    case Token::BITVEC: return "bitvec";
    case Token::CONCAT: return "concat";
    case Token::CONST: return "const";
    case Token::CONSTRAINT: return "constraint";
    case Token::CONSTD: return "constd";
    case Token::CONSTH: return "consth";
    case Token::DEC: return "dec";
    case Token::EQ: return "eq";
    case Token::FAIR: return "fair";
    case Token::IFF: return "iff";
    case Token::IMPLIES: return "implies";
    case Token::INC: return "inc";
    case Token::INIT: return "init";
    case Token::INPUT: return "input";
    case Token::ITE: return "ite";
    case Token::JUSTICE: return "justice";
    case Token::MUL: return "mul";
    case Token::NAND: return "nand";
    case Token::NEQ: return "neq";
    case Token::NEG: return "neg";
    case Token::NEGO: return "nego";
    case Token::NEXT: return "next";
    case Token::NOR: return "nor";
    case Token::NOT: return "not";
    case Token::ONE: return "one";
    case Token::ONES: return "ones";
    case Token::OR: return "or";
    case Token::OUTPUT: return "output";
    case Token::READ: return "read";
    case Token::REDAND: return "redand";
    case Token::REDOR: return "redor";
    case Token::REDXOR: return "redxor";
    case Token::ROL: return "rol";
    case Token::ROR: return "ror";
    case Token::SADDO: return "saddo";
    case Token::SDIV: return "sdiv";
    case Token::SDIVO: return "sdivo";
    case Token::SEXT: return "sext";
    case Token::SGT: return "sgt";
    case Token::SGTE: return "sgte";
    case Token::SLICE: return "slice";
    case Token::SLL: return "sll";
    case Token::SLT: return "slt";
    case Token::SLTE: return "slte";
    case Token::SORT: return "sort";
    case Token::SMOD: return "smod";
    case Token::SMULO: return "smulo";
    case Token::SRA: return "sra";
    case Token::SREM: return "rem";
    case Token::SRL: return "srl";
    case Token::SSUBO: return "ssubo";
    case Token::STATE: return "state";
    case Token::SUB: return "sub";
    case Token::UADDO: return "uaddo";
    case Token::UDIV: return "udiv";
    case Token::UEXT: return "uext";
    case Token::UGT: return "ugt";
    case Token::UGTE: return "ugte";
    case Token::ULT: return "ult";
    case Token::ULTE: return "ulte";
    case Token::UMULO: return "umulo";
    case Token::UREM: return "urem";
    case Token::USUBO: return "usubo";
    case Token::WRITE: return "write";
    case Token::XNOR: return "xnor";
    case Token::XOR: return "xor";
    case Token::ZERO: return "zero";
  }
  return "<unsupported token>";
}
}
