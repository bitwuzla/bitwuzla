#include "parser/btor2/parser.h"

#include "bv/bitvector.h"

namespace bzla {
namespace parser::btor2 {

/* Parser public ------------------------------------------------------------ */

Parser::Parser(bitwuzla::Options& options, const std::string& infile_name)
    : bzla::parser::Parser(options, infile_name)
{
  init();
}

Parser::Parser(bitwuzla::Options& options,
               const std::string& infile_name,
               FILE* infile)
    : bzla::parser::Parser(options, infile_name, infile)
{
  init();
}

Parser::~Parser()
{
  if (d_btor2_parser)
  {
    btor2parser_delete(d_btor2_parser);
  }
}

std::string
Parser::parse(bool parse_only)
{
  (void) parse_only;

  util::Timer timer(d_statistics.time_parse);

  Log(2) << "parse " << d_infile_name;

  if (!d_error.empty())
  {
    return d_error;
  }

  std::unordered_map<uint64_t, bitwuzla::Sort> sort_map;
  std::unordered_map<uint64_t, bitwuzla::Term> term_map;

  if (!btor2parser_read_lines(d_btor2_parser, d_infile))
  {
    d_error = btor2parser_error(d_btor2_parser);
    d_done  = true;
    return d_error;
  }

  std::vector<bitwuzla::Term> args;
  std::vector<uint64_t> idxs;
  Btor2LineIterator lit = btor2parser_iter_init(d_btor2_parser);
  Btor2Line* line;
  while ((line = btor2parser_iter_next(&lit)))
  {
    bitwuzla::Term term;
    bitwuzla::Sort sort;

    if (line->id > INT32_MAX)
    {
      error("given id '" + std::to_string(line->id) + "' exceeds INT32_MAX",
            line->id);
      d_done = true;
      return d_error;
    }

    if (line->tag != BTOR2_TAG_sort && line->sort.id)
    {
      if (line->sort.id > INT32_MAX)
      {
        error("given id '" + std::to_string(line->sort.id)
                  + "' exceeds INT32_MAX",
              line->id);
        d_done = true;
        return d_error;
      }
      auto it = sort_map.find(line->sort.id);
      assert(it != sort_map.end());
      sort = it->second;
      assert(!sort.is_null());
    }

    args.clear();
    idxs.clear();
    for (uint32_t i = 0; i < line->nargs; ++i)
    {
      int64_t signed_arg   = line->args[i];
      int64_t unsigned_arg = signed_arg < 0 ? -signed_arg : signed_arg;
      auto it              = term_map.find(unsigned_arg);
      assert(it != term_map.end());
      args.push_back(signed_arg < 0 ? bitwuzla::mk_term(
                         it->second.sort().is_bool() ? bitwuzla::Kind::NOT
                                                     : bitwuzla::Kind::BV_NOT,
                         {it->second})
                                    : it->second);
    }

    bitwuzla::Kind kind = bitwuzla::Kind::CONSTANT;
    switch (line->tag)
    {
      case BTOR2_TAG_add:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_ADD;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_and:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_AND;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_concat:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_CONCAT;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_const:
        assert(args.size() == 0);
        assert(line->constant);
        if (!BitVector::fits_in_size(
                line->sort.bitvec.width, line->constant, 2))
        {
          error("'const' " + std::string(line->constant)
                    + "does not fit into bit-vector of size "
                    + std::to_string(line->sort.bitvec.width),
                line->id);
          d_done = true;
          return d_error;
        }
        term = bitwuzla::mk_bv_value(sort, line->constant, 2);
        break;

      case BTOR2_TAG_constd:
        assert(args.size() == 0);
        assert(line->constant);
        if (!BitVector::fits_in_size(
                line->sort.bitvec.width, line->constant, 10))
        {
          error("'constd' " + std::string(line->constant)
                    + "does not fit into bit-vector of size "
                    + std::to_string(line->sort.bitvec.width),
                line->id);
          d_done = true;
          return d_error;
        }
        term = bitwuzla::mk_bv_value(sort, line->constant, 10);
        break;

      case BTOR2_TAG_consth:
        assert(args.size() == 0);
        assert(line->constant);
        if (!BitVector::fits_in_size(
                line->sort.bitvec.width, line->constant, 16))
        {
          error("'consth' " + std::string(line->constant)
                    + "does not fit into bit-vector of size "
                    + std::to_string(line->sort.bitvec.width),
                line->id);
          d_done = true;
          return d_error;
        }
        term = bitwuzla::mk_bv_value(sort, line->constant, 16);
        break;

      case BTOR2_TAG_constraint:
        assert(args.size() == 1);
        d_bitwuzla->assert_formula(bv1_term_to_bool(args[0]));
        break;

      case BTOR2_TAG_dec:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_DEC;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_eq:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::EQUAL;
        for (auto& arg : args)
        {
          arg = bv1_term_to_bool(arg);
        }
        break;

      case BTOR2_TAG_iff:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::IFF;
        for (auto& arg : args)
        {
          arg = bv1_term_to_bool(arg);
        }
        break;

      case BTOR2_TAG_implies:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::IMPLIES;
        for (auto& arg : args)
        {
          arg = bv1_term_to_bool(arg);
        }
        break;

      case BTOR2_TAG_inc:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_INC;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_input:
        assert(args.size() == 0);
        term = bitwuzla::mk_const(sort, line->symbol ? line->symbol : "");
        break;

      case BTOR2_TAG_ite:
        assert(args.size() == 3);
        kind = bitwuzla::Kind::ITE;
        args[0] = bv1_term_to_bool(args[0]);
        break;

      case BTOR2_TAG_mul:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_MUL;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_nand:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_NAND;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_neq:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::DISTINCT;
        for (auto& arg : args)
        {
          arg = bv1_term_to_bool(arg);
        }
        break;

      case BTOR2_TAG_neg:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_NEG;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_nor:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_NOR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_not:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_NOT;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_one:
        assert(args.size() == 0);
        term = bitwuzla::mk_bv_one(sort);
        break;

      case BTOR2_TAG_ones:
        assert(args.size() == 0);
        term = bitwuzla::mk_bv_ones(sort);
        break;

      case BTOR2_TAG_or:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_OR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_output:
        error("unsupported keyword 'output'", line->id);
        d_done = true;
        return d_error;

      case BTOR2_TAG_read:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::ARRAY_SELECT;
        args[1] = bool_term_to_bv1(args[1]);
        break;

      case BTOR2_TAG_redand:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_REDAND;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_redor:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_REDOR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_redxor:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_REDXOR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_rol:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_ROL;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_ror:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_ROR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_saddo:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SADD_OVERFLOW;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sdiv:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SDIV;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sdivo:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SDIV_OVERFLOW;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sext:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_SIGN_EXTEND;
        idxs = {static_cast<uint64_t>(line->args[1])};
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sgt:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SGT;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sgte:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SGE;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_slice:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_EXTRACT;
        idxs = {static_cast<uint64_t>(line->args[1]),
                static_cast<uint64_t>(line->args[2])};
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sll:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SHL;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_slt:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SLT;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_slte:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SLE;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sort:
        if (line->sort.tag == BTOR2_TAG_SORT_bitvec)
        {
          assert(line->sort.bitvec.width);
          sort = bitwuzla::mk_bv_sort(line->sort.bitvec.width);
        }
        else
        {
          assert(line->sort.tag == BTOR2_TAG_SORT_array);
          assert(line->sort.array.index);
          if (line->sort.array.index > INT32_MAX)
          {
            error("given id '" + std::to_string(line->sort.array.index)
                      + "' exceeds INT32_MAX",
                  line->id);
            d_done = true;
            return d_error;
          }
          auto it = sort_map.find(line->sort.array.index);
          assert(it != sort_map.end());
          bitwuzla::Sort sort_index = it->second;
          assert(line->sort.array.element);
          if (line->sort.array.element > INT32_MAX)
          {
            error("given id '" + std::to_string(line->sort.array.element)
                      + "' exceeds INT32_MAX",
                  line->id);
            d_done = true;
            return d_error;
          }
          it = sort_map.find(line->sort.array.element);
          assert(it != sort_map.end());
          bitwuzla::Sort sort_element = it->second;
          sort = bitwuzla::mk_array_sort(sort_index, sort_element);
        }
        {
          auto [it, inserted] = sort_map.emplace(line->id, sort);
          assert(inserted);
        }
        break;

      case BTOR2_TAG_smod:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SMOD;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_smulo:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SMUL_OVERFLOW;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sra:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_ASHR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_srem:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SREM;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_srl:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SHR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_ssubo:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SSUB_OVERFLOW;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_sub:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_SUB;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_uaddo:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_UADD_OVERFLOW;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_udiv:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_UDIV;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_uext:
        assert(args.size() == 1);
        kind = bitwuzla::Kind::BV_ZERO_EXTEND;
        idxs = {static_cast<uint64_t>(line->args[1])};
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_ugt:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_UGT;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_ugte:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_UGE;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_ult:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_ULT;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_ulte:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_ULE;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_umulo:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_UMUL_OVERFLOW;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_urem:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_UREM;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_usubo:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_USUB_OVERFLOW;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_write:
        assert(args.size() == 3);
        kind = bitwuzla::Kind::ARRAY_STORE;
        args[1] = bool_term_to_bv1(args[1]);
        args[2] = bool_term_to_bv1(args[2]);
        break;

      case BTOR2_TAG_xnor:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_XNOR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_xor:
        assert(args.size() == 2);
        kind = bitwuzla::Kind::BV_XOR;
        for (auto& arg : args)
        {
          arg = bool_term_to_bv1(arg);
        }
        break;

      case BTOR2_TAG_zero:
        assert(args.size() == 0);
        term = bitwuzla::mk_bv_zero(sort);
        break;

      default:
        assert(line->tag == BTOR2_TAG_bad || line->tag == BTOR2_TAG_fair
               || line->tag == BTOR2_TAG_init || line->tag == BTOR2_TAG_justice
               || line->tag == BTOR2_TAG_next || line->tag == BTOR2_TAG_state);
        error("model checking extensions not supported", line->id);
        d_done = true;
        return d_error;
    }

    if (kind != bitwuzla::Kind::CONSTANT)
    {
      term = bitwuzla::mk_term(kind, args, idxs);
    }
    assert(sort.is_null() || term.is_null() || term.sort() == sort
           || (sort.is_bv() && sort.bv_size() == 1 && term.sort().is_bool())
           || (sort.is_bool() && term.sort().is_bv()
               && term.sort().bv_size() == 1));
    if (!term.is_null())
    {
      auto [it, inserted] = term_map.emplace(line->id, term);
      assert(inserted);
    }
  }
  return d_error;
}

/* Parser private ----------------------------------------------------------- */

void
Parser::init()
{
  assert(!d_btor2_parser);
  d_btor2_parser = btor2parser_new();
  init_bitwuzla();
  bitwuzla::Sort bv1 = bitwuzla::mk_bv_sort(1);
  d_bv1_one          = bitwuzla::mk_bv_one(bv1);
  d_bv1_zero         = bitwuzla::mk_bv_zero(bv1);
}

bitwuzla::Term
Parser::bool_term_to_bv1(const bitwuzla::Term& term) const
{
  if (!term.sort().is_bool()) return term;
  return bitwuzla::mk_term(bitwuzla::Kind::ITE, {term, d_bv1_one, d_bv1_zero});
}

bitwuzla::Term
Parser::bv1_term_to_bool(const bitwuzla::Term& term) const
{
  if (!term.sort().is_bv() || term.sort().bv_size() != 1)
  {
    return term;
  }
  return bitwuzla::mk_term(bitwuzla::Kind::EQUAL, {term, d_bv1_one});
}
void
Parser::error(const std::string& error_msg, int64_t line_id)
{
  d_error = d_infile_name + ":" + std::to_string(line_id) + ":0:" + error_msg;
}

/* Parser::Statistics ------------------------------------------------------- */

Parser::Statistics::Statistics()
    : time_parse(
        d_stats.new_stat<util::TimerStatistic>("parser::smt2::time_parse"))
{
}

/* -------------------------------------------------------------------------- */

}  // namespace parser::btor2
}  // namespace bzla
