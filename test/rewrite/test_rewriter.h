#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "rewrite/rewriter.h"

namespace bzla::test {

static const char* s_solver_binary = std::getenv("SOLVER_BINARY");

class TestRewriter : public ::testing::Test
{
 protected:
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

  void test_elim_rule(node::Kind kind, const Type& type)
  {
    if (s_solver_binary == nullptr)
    {
      GTEST_SKIP_("SOLVER_BINARY environment variable not set.");
    }

    size_t num_children = node::s_node_kind_info[kind].num_children;
    size_t num_indices  = node::s_node_kind_info[kind].num_indices;

    NodeManager& nm = NodeManager::get();
    std::vector<Node> children;
    std::vector<uint64_t> indices;
    if (num_children >= 1)
    {
      children.push_back(nm.mk_const(type, "a"));
    }
    if (num_children >= 2)
    {
      children.push_back(nm.mk_const(type, "b"));
    }

    if (num_indices == 1)
    {
      indices.push_back(7);
    }
    if (num_indices == 2)
    {
      indices.push_back(1);
    }

    Node node = nm.mk_node(kind, children, indices);

    std::stringstream ss;
    for (const Node& child : children)
    {
      ss << "(declare-const " << child << " " << child.type() << ")\n";
    }
    ss << "(assert (distinct " << node << " " << Rewriter().rewrite(node)
       << "))\n";
    ASSERT_EQ(check_sat(ss), "unsat");
  }
};

}  // namespace bzla::test
