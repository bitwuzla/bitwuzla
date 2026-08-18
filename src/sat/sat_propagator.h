/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_SAT_PROPAGATOR_H_INCLUDED
#define BZLA_SAT_SAT_PROPAGATOR_H_INCLUDED

#include <cstdint>
#include <vector>

namespace bzla::sat {

class Propagator;

class SatPropagator
{
 public:
  /** Propagator kinds, used to tag key(). */
  enum class Kind : uint64_t
  {
    DISTINCT_N = 1,
    EQ_DECISION,
    DISTINCT_DECISION,
  };

  /**
   * Constructor.
   * @param kind     The kind of this propagator.
   * @param node_ids Ids of the nodes this propagator was created for.
   */
  SatPropagator(Kind kind, const std::vector<uint64_t>& node_ids)
      : d_key(mk_key(kind, node_ids))
  {
  }

  virtual ~SatPropagator()                               = default;
  virtual void attach_propagator(Propagator* propagator) = 0;
  virtual void assign(int32_t lit)                       = 0;
  virtual void unassign(int32_t var)                     = 0;
  virtual bool done() const                              = 0;

  /**
   * Key identifying the constraint enforced by this propagator.
   *
   * Propagators with equal keys are interchangeable, register_propagator()
   * only keeps the first one. Built from node ids rather than CNF literals,
   * which depend on the state of the AIG/CNF encoder.
   *
   * @return The key of this propagator.
   */
  const std::vector<uint64_t>& key() const { return d_key; }

 private:
  static std::vector<uint64_t> mk_key(Kind kind,
                                      const std::vector<uint64_t>& node_ids)
  {
    std::vector<uint64_t> key{static_cast<uint64_t>(kind)};
    key.insert(key.end(), node_ids.begin(), node_ids.end());
    return key;
  }

  /** The key of this propagator. */
  const std::vector<uint64_t> d_key;
};

}  // namespace bzla::sat

#endif
