/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_BTOR2_TOKEN_H_INCLUDED
#define BZLA_PARSER_BTOR2_TOKEN_H_INCLUDED

#include <cstdint>
#include <iostream>

namespace bzla {
namespace parser::btor2 {

enum class Token
{
  INVALID,
  ENDOFFILE,
  NUMBER,
  SYMBOL,
  // BTOR2 keywords
  ADD,
  AND,
  ARRAY,
  BAD,
  BITVEC,
  CONCAT,
  CONST,
  CONSTRAINT,
  CONSTD,
  CONSTH,
  DEC,
  EQ,
  FAIR,
  IFF,
  IMPLIES,
  INC,
  INIT,
  INPUT,
  ITE,
  JUSTICE,
  MUL,
  NAND,
  NEQ,
  NEG,
  NEGO,
  NEXT,
  NOR,
  NOT,
  ONE,
  ONES,
  OR,
  OUTPUT,
  READ,
  REDAND,
  REDOR,
  REDXOR,
  ROL,
  ROR,
  SADDO,
  SDIV,
  SDIVO,
  SEXT,
  SGT,
  SGTE,
  SLICE,
  SLL,
  SLT,
  SLTE,
  SORT,
  SMOD,
  SMULO,
  SRA,
  SREM,
  SRL,
  SSUBO,
  STATE,
  SUB,
  UADDO,
  UDIV,
  UEXT,
  UGT,
  UGTE,
  ULT,
  ULTE,
  UMULO,
  UREM,
  USUBO,
  WRITE,
  XNOR,
  XOR,
  ZERO,
};

std::ostream& operator<<(std::ostream& out, Token token);
}
}

namespace std {
std::string to_string(bzla::parser::btor2::Token token);
}
#endif
