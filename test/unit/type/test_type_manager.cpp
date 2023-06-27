/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <unordered_set>

#include "test/unit/test.h"
#include "type/type.h"
#include "type/type_manager.h"

namespace bzla::test {

using namespace bzla::type;

class TestTypeManager : public TestCommon
{
};

TEST_F(TestTypeManager, ctor_dtor) { TypeManager tm; }

TEST_F(TestTypeManager, bool_type)
{
  TypeManager tm;
  Type bool_type = tm.mk_bool_type();
  ASSERT_TRUE(bool_type.is_bool());
  ASSERT_FALSE(bool_type.is_bv());
  ASSERT_FALSE(bool_type.is_fp());
  ASSERT_FALSE(bool_type.is_rm());
  ASSERT_FALSE(bool_type.is_array());
  ASSERT_FALSE(bool_type.is_fun());
  ASSERT_EQ(bool_type, tm.mk_bool_type());
}

TEST_F(TestTypeManager, bv_type)
{
  TypeManager tm;
  Type bv32 = tm.mk_bv_type(32);
  Type bv64 = tm.mk_bv_type(64);

  ASSERT_TRUE(bv32.is_bv());
  ASSERT_FALSE(bv32.is_bool());
  ASSERT_FALSE(bv32.is_fp());
  ASSERT_FALSE(bv32.is_rm());
  ASSERT_FALSE(bv32.is_array());
  ASSERT_FALSE(bv32.is_fun());

  ASSERT_EQ(bv32.bv_size(), 32);
  ASSERT_EQ(bv64.bv_size(), 64);

  ASSERT_NE(bv32, bv64);
  ASSERT_EQ(bv32, tm.mk_bv_type(32));
  ASSERT_EQ(bv64, tm.mk_bv_type(64));
}

TEST_F(TestTypeManager, fp_type)
{
  TypeManager tm;
  Type fp16 = tm.mk_fp_type(5, 11);
  Type fp32 = tm.mk_fp_type(8, 24);

  ASSERT_TRUE(fp16.is_fp());
  ASSERT_FALSE(fp16.is_bool());
  ASSERT_FALSE(fp16.is_bv());
  ASSERT_FALSE(fp16.is_rm());
  ASSERT_FALSE(fp16.is_array());
  ASSERT_FALSE(fp16.is_fun());

  ASSERT_EQ(fp16.fp_exp_size(), 5);
  ASSERT_EQ(fp16.fp_sig_size(), 11);

  ASSERT_NE(fp16, fp32);
  ASSERT_EQ(fp16, tm.mk_fp_type(5, 11));
  ASSERT_EQ(fp32, tm.mk_fp_type(8, 24));
}

TEST_F(TestTypeManager, rm_type)
{
  TypeManager tm;
  Type rm_type = tm.mk_rm_type();
  ASSERT_TRUE(rm_type.is_rm());
  ASSERT_FALSE(rm_type.is_bool());
  ASSERT_FALSE(rm_type.is_bv());
  ASSERT_FALSE(rm_type.is_fp());
  ASSERT_FALSE(rm_type.is_array());
  ASSERT_FALSE(rm_type.is_fun());
  ASSERT_EQ(rm_type, tm.mk_rm_type());
}

TEST_F(TestTypeManager, array_type)
{
  TypeManager tm;
  Type fp16       = tm.mk_fp_type(5, 11);
  Type bv32       = tm.mk_bv_type(32);
  Type array_type = tm.mk_array_type(fp16, bv32);

  ASSERT_TRUE(array_type.is_array());
  ASSERT_FALSE(array_type.is_bool());
  ASSERT_FALSE(array_type.is_bv());
  ASSERT_FALSE(array_type.is_fp());
  ASSERT_FALSE(array_type.is_rm());
  ASSERT_FALSE(array_type.is_fun());
  ASSERT_EQ(array_type, tm.mk_array_type(fp16, bv32));
  ASSERT_NE(array_type, tm.mk_array_type(bv32, fp16));
  ASSERT_NE(array_type, fp16);
  ASSERT_NE(array_type, bv32);
}

TEST_F(TestTypeManager, array_type_nested)
{
  TypeManager tm;
  Type fp16        = tm.mk_fp_type(5, 11);
  Type bv32        = tm.mk_bv_type(32);
  Type array_type  = tm.mk_array_type(fp16, bv32);
  Type array_type2 = tm.mk_array_type(bv32, array_type);

  ASSERT_TRUE(array_type.is_array());
  ASSERT_FALSE(array_type.is_bool());
  ASSERT_FALSE(array_type.is_bv());
  ASSERT_FALSE(array_type.is_fp());
  ASSERT_FALSE(array_type.is_rm());
  ASSERT_FALSE(array_type.is_fun());
  ASSERT_EQ(array_type2, tm.mk_array_type(bv32, array_type));
  ASSERT_NE(array_type2, array_type);
  ASSERT_NE(array_type, fp16);
  ASSERT_NE(array_type, bv32);
}

TEST_F(TestTypeManager, fun_type)
{
  TypeManager tm;
  Type fp16       = tm.mk_fp_type(5, 11);
  Type bv32       = tm.mk_bv_type(32);
  Type bool_type  = tm.mk_bool_type();
  Type rm_type    = tm.mk_rm_type();
  Type array_type = tm.mk_array_type(fp16, bool_type);
  Type fun_type =
      tm.mk_fun_type({fp16, bv32, bool_type, rm_type, fp16, bv32, array_type});

  ASSERT_TRUE(fun_type.is_fun());
  ASSERT_FALSE(fun_type.is_bool());
  ASSERT_FALSE(fun_type.is_bv());
  ASSERT_FALSE(fun_type.is_fp());
  ASSERT_FALSE(fun_type.is_rm());
  ASSERT_FALSE(fun_type.is_array());
  ASSERT_EQ(
      fun_type,
      tm.mk_fun_type({fp16, bv32, bool_type, rm_type, fp16, bv32, array_type}));
  ASSERT_NE(fun_type, tm.mk_array_type(bv32, fp16));
  ASSERT_NE(fun_type, tm.mk_fun_type({bool_type, array_type}));
  ASSERT_NE(fun_type, fp16);
  ASSERT_NE(fun_type, bv32);
}

TEST_F(TestTypeManager, hash_type)
{
  TypeManager tm;

  Type fp16       = tm.mk_fp_type(5, 11);
  Type bv32       = tm.mk_bv_type(32);
  Type bool_type  = tm.mk_bool_type();
  Type rm_type    = tm.mk_rm_type();
  Type array_type = tm.mk_array_type(fp16, bool_type);

  Type fp16_2 = tm.mk_fp_type(5, 11);

  std::unordered_set<Type> set;
  set.insert(fp16);
  set.insert(bv32);
  set.insert(array_type);
  ASSERT_TRUE(set.count(fp16) > 0);
  ASSERT_TRUE(set.count(fp16_2) > 0);
  ASSERT_TRUE(set.count(bv32) > 0);
  ASSERT_TRUE(set.count(array_type) > 0);
  ASSERT_FALSE(set.count(bool_type) > 0);
}

}  // namespace bzla::test
