/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "env.h"
#include "gtest/gtest.h"
#include "node/kind_info.h"
#include "node/node_manager.h"
#include "rewrite/rewriter.h"
#include "solver/fp/floating_point.h"

namespace bzla::test {

static const char* s_solver_binary = std::getenv("SOLVER_BINARY");

class TestRewriter : public ::testing::Test
{
 protected:
  TestRewriter() : d_rewriter(d_env.rewriter()) {}

  void SetUp() override
  {
    d_bool_type = d_nm.mk_bool_type();
    d_bv4_type  = d_nm.mk_bv_type(4);
    d_bv1_type  = d_nm.mk_bv_type(1);
    d_fp35_type = d_nm.mk_fp_type(3, 5);
    d_rm_type   = d_nm.mk_rm_type();

    d_a = d_nm.mk_const(d_nm.mk_bool_type(), "a");
    d_b = d_nm.mk_const(d_nm.mk_bool_type(), "b");
    d_c = d_nm.mk_const(d_nm.mk_bool_type(), "c");
    d_d = d_nm.mk_const(d_nm.mk_bool_type(), "d");

    d_bv4_zero  = d_nm.mk_value(BitVector::mk_zero(4));
    d_bv1_zero  = d_nm.mk_value(BitVector::mk_zero(1));
    d_bv4_one   = d_nm.mk_value(BitVector::mk_one(4));
    d_bv1_one   = d_nm.mk_value(BitVector::mk_one(1));
    d_bv4_ones  = d_nm.mk_value(BitVector::mk_ones(4));
    d_bv1_ones  = d_nm.mk_value(BitVector::mk_ones(1));

    d_bv4_a = d_nm.mk_const(d_bv4_type, "a_bv4");
    d_bv4_b = d_nm.mk_const(d_bv4_type, "b_bv4");
    d_bv4_c = d_nm.mk_const(d_bv4_type, "c_bv4");
    d_bv4_d = d_nm.mk_const(d_bv4_type, "d_bv4");
    d_bv1_a = d_nm.mk_const(d_bv1_type, "a_bv1");
    d_bv1_b = d_nm.mk_const(d_bv1_type, "b_bv1");

    d_fp35_pzero = d_nm.mk_value(FloatingPoint::fpzero(d_fp35_type, false));
    d_fp35_nzero = d_nm.mk_value(FloatingPoint::fpzero(d_fp35_type, true));

    d_fp35_a = d_nm.mk_const(d_fp35_type, "a_fp35");
    d_fp35_b = d_nm.mk_const(d_fp35_type, "b_fp35");

    d_rm = d_nm.mk_const(d_rm_type, "rm");

    d_false     = d_nm.mk_value(false);
    d_true      = d_nm.mk_value(true);
  }

  static std::string check_sat(std::stringstream& ss)
  {
    std::stringstream bench;
    bench << "(set-logic QF_BV)\n";
    bench << "(set-option :produce-models true)\n";
    bench << ss.str();
    bench << "(check-sat)\n";
    bench << "(get-model)\n";

    char filename[] = "bzlarwtest-XXXXXX";
    int fd          = mkstemp(filename);
    assert(fd != -1);

    FILE* file = fdopen(fd, "w");
    fputs(bench.str().c_str(), file);
    fflush(file);

    std::stringstream cmd;
    cmd << s_solver_binary << " " << filename;

    // Execute solver and read output.
    FILE* fp = popen(cmd.str().c_str(), "r");
    char buf[1024];
    std::stringstream output;
    while (fgets(buf, 1024, fp))
    {
      output << buf;
    }
    remove(filename);
    fclose(file);

    std::string result = output.str();
    size_t newline_pos = result.find_last_of('\n');
    return result.substr(0, newline_pos);
  }

  void test_elim_rule(node::Kind kind,
                      const Type& type,
                      const std::vector<uint64_t>& indices = {})
  {
    if (s_solver_binary == nullptr)
    {
      GTEST_SKIP_("SOLVER_BINARY environment variable not set.");
    }

    size_t num_children = node::KindInfo::num_children(kind);
    size_t num_indices  = node::KindInfo::num_indices(kind);
    ASSERT_EQ(indices.size(), num_indices);

    NodeManager& nm = NodeManager::get();
    std::vector<Node> children;
    if (kind == node::Kind::FP_SUB)
    {
      children.push_back(nm.mk_const(nm.mk_rm_type()));
      children.push_back(nm.mk_const(type, "a"));
      children.push_back(nm.mk_const(type, "b"));
    }
    else if (kind == node::Kind::FP_FP)
    {
      children.push_back(nm.mk_const(nm.mk_bv_type(1), "sign"));
      children.push_back(nm.mk_const(nm.mk_bv_type(type.fp_exp_size()), "exp"));
      children.push_back(
          nm.mk_const(nm.mk_bv_type(type.fp_sig_size() - 1), "sig"));
    }
    else
    {
      if (num_children >= 1)
      {
        children.push_back(nm.mk_const(type, "a"));
      }
      if (num_children >= 2)
      {
        children.push_back(nm.mk_const(type, "b"));
      }
    }

    Node node = nm.mk_node(kind, children, indices);

    std::stringstream ss;
    for (const Node& child : children)
    {
      ss << "(declare-const " << child << " " << child.type() << ")\n";
    }
    Env env;
    ss << "(assert (distinct " << node << " " << env.rewriter().rewrite(node)
       << "))\n";
    ASSERT_EQ(check_sat(ss), "unsat");
  }

  template <RewriteRuleKind K>
  void test_rule(const Node& node)
  {
    if (s_solver_binary == nullptr)
    {
      GTEST_SKIP_("SOLVER_BINARY environment variable not set.");
    }
    Env env;
    Rewriter& rewriter = env.rewriter();
    std::stringstream ss;
    std::vector<std::reference_wrapper<const Node>> visit{node};
    std::unordered_set<Node> visited;
    do
    {
      const Node& cur = visit.back();
      visit.pop_back();
      auto [it, inserted] = visited.emplace(cur);
      if (inserted)
      {
        if (cur.is_const())
        {
          ss << "(declare-const " << cur << " " << cur.type() << ")\n";
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    } while (!visit.empty());
    Node res;
    RewriteRuleKind kind;
    std::tie(res, kind) = RewriteRule<K>::apply(rewriter, node);
    if (res == node)
    {
      std::cout << "node: " << node << std::endl;
    }
    ASSERT_NE(node, res);
    ss << "(assert (distinct " << node << " " << res << "))\n";
    ASSERT_EQ(check_sat(ss), "unsat");
  }

  template <RewriteRuleKind K>
  void test_rule_does_not_apply(const Node& node)
  {
    ASSERT_EQ(node, RewriteRule<K>::apply(d_rewriter, node).first);
  }

  void test_rewrite(const Node& node, const Node& expected)
  {
    Env env;
    ASSERT_EQ(expected, d_rewriter.rewrite(node));
    ASSERT_EQ(expected, env.rewriter().rewrite(node));
  }

  Env d_env;
  Rewriter& d_rewriter;

  NodeManager& d_nm = NodeManager::get();

  Type d_bool_type;
  Type d_bv4_type;
  Type d_bv1_type;
  Type d_fp35_type;
  Type d_rm_type;

  Node d_a;
  Node d_b;
  Node d_c;
  Node d_d;

  Node d_bv4_zero;
  Node d_bv1_zero;
  Node d_bv1_one;
  Node d_bv4_one;
  Node d_bv1_ones;
  Node d_bv4_ones;

  Node d_bv1_a;
  Node d_bv1_b;
  Node d_bv4_a;
  Node d_bv4_b;
  Node d_bv4_c;
  Node d_bv4_d;

  Node d_fp35_pzero;
  Node d_fp35_nzero;

  Node d_fp35_a;
  Node d_fp35_b;

  Node d_rm;

  Node d_false;
  Node d_true;
};

}  // namespace bzla::test
