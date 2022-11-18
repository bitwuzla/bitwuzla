#ifndef BZLA_SOLVER_FUN_FUN_SOLVER_H_INCLUDED
#define BZLA_SOLVER_FUN_FUN_SOLVER_H_INCLUDED

#include "backtrack/vector.h"
#include "option/option.h"
#include "solver/solver.h"

namespace bzla::fun {

class FunSolver : public Solver
{
 public:
  /** Determine if `term` is a leaf node for the function solver. */
  static bool is_leaf(const Node& term);

  FunSolver(SolverEngine& solver_engine);
  ~FunSolver();

  void check() override;

  Node value(const Node& term) override;

  void register_term(const Node& term) override;

 private:
  /** Adds function congruence lemma between function applications a and b. */
  void add_function_congruence_lemma(const Node& a, const Node& b);

  /** Registered function applications. */
  backtrack::vector<Node> d_applies;

  /**
   * Utility class used to store function applications in d_fun_models.
   *
   * An Apply class is hashed and compared based on the current model value of
   * the function application's arguments.
   *
   * @note: This class caches model values and hash values in order to avoid
   *        repeatedly querying and computing the hash values when accessing a
   *        function model.
   */
  class Apply
  {
   public:
    Apply(const Node& apply, SolverEngine& solver_engine);

    /** @return Associated function application. */
    const Node& get() const;

    /** @return Value of associated function application. */
    const Node& value() const;

    /** @return Values of function application arguments. */
    const std::vector<Node>& values() const;

    /** Compare two function applications based on d_values. */
    bool operator==(const Apply& other) const;

    /** Compute hash value based on d_values. */
    size_t hash() const;

   private:
    /** Associated function application. */
    const Node& d_apply;
    /** Cached hash value. */
    size_t d_hash;
    /** Value of the function application. */
    Node d_value;
    /** Values of function arguments. */
    std::vector<Node> d_values;
  };

  /** Hash struct for hashing Apply. */
  struct HashApply
  {
    size_t operator()(const Apply& apply) const { return apply.hash(); }
  };

  /** Function models constructed during check(). */
  std::unordered_map<Node, std::unordered_set<Apply, HashApply>> d_fun_models;
};

}  // namespace bzla::fun

#endif
