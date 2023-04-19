#ifndef BITWUZLA_API_C_CHECKS_H_INCLUDED
#define BITWUZLA_API_C_CHECKS_H_INCLUDED

/* -------------------------------------------------------------------------- */

class AbortStream
{
 public:
  AbortStream(const std::string &msg_prefix) { stream() << msg_prefix << " "; }
  [[noreturn]] ~AbortStream()
  {
    flush();
    std::abort();
  }
  AbortStream(const AbortStream &astream) = default;

  std::ostream &stream() { return std::cerr; }

 private:
  void flush()
  {
    stream() << std::endl;
    stream().flush();
  }
};

#define BITWUZLA_ABORT \
  bzla::util::OstreamVoider() & AbortStream("bitwuzla: error: ").stream()

#define BITWUZLA_TRY_CATCH_BEGIN \
  try                            \
  {
#define BITWUZLA_TRY_CATCH_END \
  }                            \
  catch (bitwuzla::Exception & e) { BITWUZLA_ABORT << e.msg(); }

/* -------------------------------------------------------------------------- */

#define BITWUZLA_CHECK_SORT_ID(sort_id)             \
  BITWUZLA_CHECK(Bitwuzla::sort_map().find(sort_id) \
                 != Bitwuzla::sort_map().end())     \
      << "invalid sort id";

#define BITWUZLA_CHECK_SORT_ID_AT_IDX(sorts, i)        \
  BITWUZLA_CHECK(Bitwuzla::sort_map().find((sorts)[i]) \
                 != Bitwuzla::sort_map().end())        \
      << "invalid sort id at index " << i;

#define BITWUZLA_CHECK_TERM_ID(term_id)             \
  BITWUZLA_CHECK(Bitwuzla::term_map().find(term_id) \
                 != Bitwuzla::term_map().end())     \
      << "invalid term id";

#define BITWUZLA_CHECK_TERM_ID_AT_IDX(terms, i)        \
  BITWUZLA_CHECK(Bitwuzla::term_map().find((terms)[i]) \
                 != Bitwuzla::term_map().end())        \
      << "invalid term id at index " << i;

#define BITWUZLA_CHECK_RM(rm) \
  BITWUZLA_CHECK((rm) < BITWUZLA_RM_MAX) << "invalid rounding mode";

#define BITWUZLA_CHECK_KIND(kind) \
  BITWUZLA_CHECK((kind) < BITWUZLA_KIND_NUM_KINDS) << "invalid term kind";

#define BITWUZLA_CHECK_OPTION(opt) \
  BITWUZLA_CHECK((opt) < BITWUZLA_OPT_NUM_OPTS) << "invalid option";

#define BITWUZLA_CHECK_RESULT(result)                                   \
  BITWUZLA_CHECK((result) == BITWUZLA_SAT || (result) == BITWUZLA_UNSAT \
                 || (result) == BITWUZLA_UNKNOWN)                       \
      << "invalid result";

#endif
