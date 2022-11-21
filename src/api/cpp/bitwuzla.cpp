#include "api/cpp/bitwuzla.h"

namespace bitwuzla {

/* -------------------------------------------------------------------------- */

std::ostream &operator<<(std::ostream &out, Result result);
std::ostream &operator<<(std::ostream &out, Kind kind);
std::ostream &operator<<(std::ostream &out, RoundingMode rm);

/* Options public ----------------------------------------------------------- */

void
Options::set(Option option, uint64_t value)
{
  // TODO
}

void
Options::set(Option option, const std::string &mode)
{
  // TODO
}

uint64_t
Options::get_numeric(Option option) const
{
  // TODO
}

bool
Options::get_bool(Option option) const
{
  // TODO
}

const std::string &
Options::get_mode(Option option) const
{
  // TODO
}

const OptionInfo &
Options::get_info(Option option) const
{
  // TODO
}

/* Term public -------------------------------------------------------------- */

Kind
Term::kind() const
{
  // TODO
}

const Sort &
Term::sort() const
{
  // TODO
}

size_t
Term::num_children() const
{
  // TODO
}

const std::vector<Term> &
Term::children() const
{
  // TODO
}

const std::vector<uint32_t> &
Term::indices() const
{
  // TODO
}

bool
Term::is_indexed() const
{
  // TODO
}

const std::string &
Term::symbol() const
{
  // TODO
}

void
Term::set_symbol(const std::string &symbol)
{
  // TODO
}

bool
Term::is_const() const
{
  // TODO
}

bool
Term::is_var() const
{
  // TODO
}

bool
Term::is_value() const
{
  // TODO
}

bool
Term::is_bv_value_zero() const
{
  // TODO
}

bool
Term::is_bv_value_one() const
{
  // TODO
}

bool
Term::is_bv_value_ones() const
{
  // TODO
}

bool
Term::is_bv_value_min_signed() const
{
  // TODO
}

bool
Term::is_bv_value_max_signed() const
{
  // TODO
}

bool
Term::is_fp_value_pos_zero() const
{
  // TODO
}

bool
Term::is_fp_value_neg_zero() const
{
  // TODO
}

bool
Term::is_fp_value_pos_inf() const
{
  // TODO
}

bool
Term::is_fp_value_neg_inf() const
{
  // TODO
}

bool
Term::is_fp_value_nan() const
{
  // TODO
}

bool
Term::is_rm_value_rna() const
{
  // TODO
}

bool
Term::is_rm_value_rne() const
{
  // TODO
}

bool
Term::is_rm_value_rtn() const
{
  // TODO
}

bool
Term::is_rm_value_rtp() const
{
  // TODO
}

bool
Term::is_rm_value_rtz() const
{
  // TODO
}

bool
Term::is_const_array() const
{
  // TODO
}

void
Term::str(const std::string &format)
{
  // TODO
}

bool
operator==(const Term &a, const Term &b)
{
  // TODO
}

std::ostream &
operator<<(std::ostream &out, const Term &term)
{
  // TODO
}

/* Sort public -------------------------------------------------------------- */

uint64_t
Sort::bv_size() const
{
  // TODO
}

uint64_t
Sort::fp_exp_size() const
{
  // TODO
}

uint64_t
Sort::fp_sig_size() const
{
  // TODO
}

const Sort &
Sort::array_get_index() const
{
  // TODO
}

const Sort &
Sort::array_get_element() const
{
  // TODO
}

std::vector<Sort>
Sort::fun_get_domain() const
{
  // TODO
}

const Sort &
Sort::fun_get_codomain() const
{
  // TODO
}

size_t
Sort::fun_arity() const
{
  // TODO
}

bool
Sort::is_array() const
{
  // TODO
}

bool
Sort::is_bool() const
{
  // TODO
}

bool
Sort::is_bv() const
{
  // TODO
}

bool
Sort::is_fp() const
{
  // TODO
}

bool
Sort::is_fun() const
{
  // TODO
}

bool
Sort::is_rm() const
{
  // TODO
}

std::string
Sort::str() const
{
  // TODO
}

bool
operator==(const Sort &a, const Sort &b)
{
  // TODO
}

std::ostream &
operator<<(std::ostream &out, const Sort &sort)
{
  // TODO
}

/* Bitwuzla public ---------------------------------------------------------- */

Bitwuzla::Bitwuzla(const Options &options)
{
  // TODO
}

Bitwuzla::~Bitwuzla()
{
  // TODO
}

bool
Bitwuzla::terminate()
{
  // TODO
}

void
Bitwuzla::set_termination_callback(std::function<int32_t(void *)> fun,
                                   void *state)
{
  // TODO
}

void *
Bitwuzla::get_termination_callback_state()
{
  // TODO
}

void
Bitwuzla::set_abort_callback(std::function<void(const std::string &)> fun)
{
  // TODO
}

void
Bitwuzla::push(uint32_t nlevels)
{
  // TODO
}

void
Bitwuzla::pop(uint32_t nlevels)
{
  // TODO
}

void
Bitwuzla::assert_formula(const Term &term)
{
  // TODO
}

void
Bitwuzla::assume_formula(const Term &term)
{
  // TODO
}

bool
Bitwuzla::is_unsat_assumption(const Term &term)
{
  // TODO
}

std::vector<Term>
Bitwuzla::bitwuzla_get_unsat_assumptions()
{
  // TODO
}

std::vector<Term>
Bitwuzla::bitwuzla_get_unsat_core()
{
  // TODO
}

void
Bitwuzla::reset_assumptions()
{
  // TODO
}

Result
Bitwuzla::simplify()
{
  // TODO
}

Result
Bitwuzla::check_sat()
{
  // TODO
}

const Term &
Bitwuzla::get_value(const Term &term)
{
  // TODO
}

std::string
Bitwuzla::get_bv_value(const Term &term)
{
  // TODO
}

void
Bitwuzla::get_fp_value(const Term &term,
                       std::string &sign,
                       std::string &exponent,
                       std::string &significand)
{
  // TODO
}

std::string
Bitwuzla::get_rm_value(const Term &term)
{
  // TODO
}

void
Bitwuzla::get_array_value(const Term &term,
                          std::vector<Term> &indices,
                          std::vector<Term> &values,
                          Term &default_value)
{
  // TODO
}

void
Bitwuzla::get_fun_value(const Term &term,
                        std::vector<std::vector<Term>> args,
                        std::vector<Term> values)
{
  // TODO
}

void
Bitwuzla::print_model(std::ostream &out, const std::string &format)
{
  // TODO
}

void
Bitwuzla::dump_formula(std::ostream &out, const std::string &format)
{
  // TODO
}

Result
Bitwuzla::parse(std::ifstream &infile,
                const std::string &infile_name,
                std::string &error_msg,
                Result &status,
                bool &is_smt2)
{
  // TODO
}

Result
Bitwuzla::parse(const std::string &format,
                std::ifstream &infile,
                const std::string &infile_name,
                std::string &error_msg,
                Result &status,
                bool &is_smt2)
{
  // TODO
}

/* -------------------------------------------------------------------------- */

Sort
mk_array_sort(const Sort &index, const Sort &element)
{
  // TODO
}

Sort
mk_bool_sort()
{
  // TODO
}

Sort
mk_bv_sort(uint64_t size)
{
  // TODO
}

Sort
mk_fp_sort(uint64_t exp_size, uint64_t sig_size)
{
  // TODO
}

Sort
mk_fun_sort(const std::vector<Sort> &domain, const Sort &codomain)
{
  // TODO
}

Sort
mk_rm_sort()
{
  // TODO
}

Term
mk_true()
{
  // TODO
}

Term
mk_false()
{
  // TODO
}

Term
mk_bv_zero(const Sort &sort)
{
  // TODO
}

Term
mk_bv_one(const Sort &sort)
{
  // TODO
}

Term
mk_bv_ones(const Sort &sort)
{
  // TODO
}

Term
mk_bv_min_signed(const Sort &sort)
{
  // TODO
}

Term
mk_bv_max_signed(const Sort &sort)
{
  // TODO
}

Term
mk_fp_pos_zero(const Sort &sort)
{
  // TODO
}

Term
mk_fp_neg_zero(const Sort &sort)
{
  // TODO
}

Term
mk_fp_pos_inf(const Sort &sort)
{
  // TODO
}

Term
mk_fp_neg_inf(const Sort &sort)
{
  // TODO
}

Term
mk_fp_nan(const Sort &sort)
{
  // TODO
}

Term
mk_bv_value(const Sort &sort, const std::string &value, uint8_t base)
{
  // TODO
}

Term
mk_bv_value_uint64(const Sort &sort, uint64_t value)
{
  // TODO
}

Term
mk_bv_value_int64(const Sort &sort, int64_t value)
{
  // TODO
}

Term
mk_fp_value(const Term &bv_sign,
            const Term &bv_exponent,
            const Term &bv_significand)
{
  // TODO
}

Term
mk_fp_value_from_real(const Sort &sort, const Term &rm, const std::string &real)
{
  // TODO
}

Term
mk_fp_value_from_rational(const Sort &sort,
                          const Term &rm,
                          const std::string &num,
                          const std::string &den)
{
  // TODO
}

Term
mk_rm_value(RoundingMode rm)
{
  // TODO
}

Term
mk_term(Kind kind,
        const std::vector<Term> &args,
        const std::vector<uint64_t> indices)
{
  // TODO
}

Term
mk_const(const Sort &sort, const std::string &symbol)
{
  // TODO
}

Term
mk_var(const Sort &sort, const std::string &symbol)
{
  // TODO
}

Term
substitute_term(const Term &term, const std::unordered_map<Term, Term> map)
{
  // TODO
}

void
substitute_terms(std::vector<Term> &terms,
                 const std::unordered_map<Term, Term> map)
{
  // TODO
}

/* -------------------------------------------------------------------------- */
}  // namespace bitwuzla
/* -------------------------------------------------------------------------- */

namespace std {

size_t
std::hash<bitwuzla::Sort>::operator()(const bitwuzla::Sort &sort) const
{
  // TODO
}

size_t
std::hash<bitwuzla::Term>::operator()(const bitwuzla::Term &term) const
{
  // TODO
}

}  // namespace std
