#include "node/node.h"
#include "node/node_manager.h"
#include "test.h"

namespace bzla::test {

using namespace bzla::node;
using namespace bzla::type;

class TestNodeManager : public TestCommon
{
};

/* --- Node tests ---------------------------------------------------------- */

TEST_F(TestNodeManager, node_ctor_dtor)
{
  Node n;
  ASSERT_TRUE(n.is_null());
  ASSERT_EQ(n.get_kind(), Kind::NULL_NODE);
  ASSERT_EQ(n.get_id(), 0);
  ASSERT_EQ(n.get_num_children(), 0);
  ASSERT_EQ(n.begin(), n.end());
}

/* --- NodeManager tests --------------------------------------------------- */

TEST_F(TestNodeManager, ctor_dtor) { NodeManager nm; }

TEST_F(TestNodeManager, mk_const)
{
  NodeManager nm;

  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fp_type    = nm.mk_fp_type(5, 11);
  Type rm_type    = nm.mk_rm_type();
  Type array_type = nm.mk_array_type(bv_type, fp_type);
  Type fun_type   = nm.mk_fun_type({bool_type, rm_type, array_type});

  Node bool_const  = nm.mk_const(bool_type);
  Node bv_const    = nm.mk_const(bv_type);
  Node fp_const    = nm.mk_const(fp_type);
  Node rm_const    = nm.mk_const(rm_type);
  Node array_const = nm.mk_const(array_type);
  Node fun_const   = nm.mk_const(fun_type);

  ASSERT_NE(bool_const, nm.mk_const(bool_type));
  ASSERT_NE(bv_const, nm.mk_const(bv_type));
  ASSERT_NE(fp_const, nm.mk_const(fp_type));
  ASSERT_NE(rm_const, nm.mk_const(rm_type));
  ASSERT_NE(array_const, nm.mk_const(array_type));
  ASSERT_NE(fun_const, nm.mk_const(fun_type));

  ASSERT_EQ(bool_const.get_kind(), Kind::CONSTANT);
  ASSERT_EQ(bool_const.get_num_children(), 0);
  ASSERT_TRUE(bool_const.get_type().is_bool());

  ASSERT_EQ(bv_const.get_kind(), Kind::CONSTANT);
  ASSERT_EQ(bv_const.get_num_children(), 0);
  ASSERT_TRUE(bv_const.get_type().is_bv());

  ASSERT_EQ(fp_const.get_kind(), Kind::CONSTANT);
  ASSERT_EQ(fp_const.get_num_children(), 0);
  ASSERT_TRUE(fp_const.get_type().is_fp());

  ASSERT_EQ(rm_const.get_kind(), Kind::CONSTANT);
  ASSERT_EQ(rm_const.get_num_children(), 0);
  ASSERT_TRUE(rm_const.get_type().is_rm());

  ASSERT_EQ(array_const.get_kind(), Kind::CONSTANT);
  ASSERT_EQ(array_const.get_num_children(), 0);
  ASSERT_TRUE(array_const.get_type().is_array());

  ASSERT_EQ(fun_const.get_kind(), Kind::CONSTANT);
  ASSERT_EQ(fun_const.get_num_children(), 0);
  ASSERT_TRUE(fun_const.get_type().is_fun());
};

// TODO: mk_value

TEST_F(TestNodeManager, mk_node)
{
  NodeManager nm;

  Type bool_type = nm.mk_bool_type();

  Node x = nm.mk_const(bool_type);
  Node y = nm.mk_const(bool_type);
  Node z = nm.mk_const(bool_type);

  Node x_and_y = nm.mk_node(Kind::AND, {x, y});

  ASSERT_EQ(x_and_y.get_num_children(), 2);
  ASSERT_NE(x_and_y.begin(), x_and_y.end());
  ASSERT_EQ(x_and_y[0], x);
  ASSERT_EQ(x_and_y[1], y);
  for (auto it = x_and_y.begin(); it != x_and_y.end(); ++it)
  {
    ASSERT_FALSE(it->is_null());
    ASSERT_TRUE(*it == x || *it == y);
  }
  for (const Node& c : x_and_y)
  {
    ASSERT_FALSE(c.is_null());
    ASSERT_TRUE(c == x || c == y);
  }

  Node or_z = nm.mk_node(Kind::OR, {x_and_y, z});

  ASSERT_EQ(x_and_y, nm.mk_node(Kind::AND, {x, y}));
  ASSERT_EQ(or_z, nm.mk_node(Kind::OR, {nm.mk_node(Kind::AND, {x, y}), z}));
};

TEST_F(TestNodeManager, mk_apply)
{
  NodeManager nm;

  Type bool_type  = nm.mk_bool_type();
  Type fun_type   = nm.mk_fun_type({bool_type,
                                    bool_type,
                                    bool_type,
                                    bool_type,
                                    bool_type,
                                    bool_type,
                                    bool_type});
  Node fun        = nm.mk_const(fun_type);
  Node bool_const = nm.mk_const(bool_type);
  Node apply      = nm.mk_node(Kind::APPLY,
                          {fun,
                                bool_const,
                                bool_const,
                                bool_const,
                                bool_const,
                                bool_const,
                                bool_const});

  ASSERT_EQ(apply.get_num_children(), 7);
  ASSERT_EQ(apply,
            nm.mk_node(Kind::APPLY,
                       {fun,
                        bool_const,
                        bool_const,
                        bool_const,
                        bool_const,
                        bool_const,
                        bool_const}));
  ASSERT_EQ(apply[0], fun);
  for (size_t i = 1; i < apply.get_num_children(); ++i)
  {
    ASSERT_EQ(apply[i], bool_const);
  }
}

}  // namespace bzla::test
