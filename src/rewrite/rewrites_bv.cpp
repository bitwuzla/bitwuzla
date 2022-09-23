#include "rewrite/rewrites_bv.h"

#include "bitvector.h"
#include "node/node_manager.h"

namespace bzla {

using namespace node;

/* bvadd -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvadd(node[1].value<BitVector>()));
  return res;
}

/* bvand -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_AND_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvand(node[1].value<BitVector>()));
  return res;
}

/* bvashr ------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_ASHR_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvashr(node[1].value<BitVector>()));
  return res;
}

/* bvconcat ----------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_CONCAT_EVAL>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvconcat(node[1].value<BitVector>()));
  return res;
}

/* bvmul -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_MUL_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvmul(node[1].value<BitVector>()));
  return res;
}

/* bvshl -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_SHL_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvshl(node[1].value<BitVector>()));
  return res;
}

/* bvshr -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_SHR_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvshr(node[1].value<BitVector>()));
  return res;
}

/* bvslt -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_SLT_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().signed_compare(node[1].value<BitVector>())
      < 0);
  return res;
}

/* bvudiv ------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_UDIV_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvudiv(node[1].value<BitVector>()));
  return res;
}

/* bvult -------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_ULT_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().compare(node[1].value<BitVector>()) < 0);
  return res;
}

/* bvudiv ------------------------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_UREM_EVAL>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  (void) rewriter;
  assert(node.num_children() == 2);
  if (!node[0].is_value() || !node[1].is_value()) return node;
  Node res = NodeManager::get().mk_value(
      node[0].value<BitVector>().bvurem(node[1].value<BitVector>()));
  return res;
}

/* --- Elimination Rules ---------------------------------------------------- */

template <>
Node
RewriteRule<RewriteRuleKind::BV_NAND_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  return rewriter.mk_node(Kind::BV_NOT,
                          {rewriter.mk_node(Kind::BV_AND, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_ADD,
      {rewriter.mk_node(Kind::BV_NOT, {node[0]}),
       NodeManager::get().mk_value(BitVector::mk_one(node.type().bv_size()))});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_NOR_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_NOT,
                          {rewriter.mk_node(Kind::BV_OR, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_OR_ELIM>::_apply(Rewriter& rewriter,
                                                 const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_NOT,
      {rewriter.mk_node(Kind::BV_AND,
                        {rewriter.mk_node(Kind::BV_NOT, {node[0]}),
                         rewriter.mk_node(Kind::BV_NOT, {node[1]})})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REDAND_ELIM>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  return rewriter.mk_node(Kind::BV_COMP,
                          {node[0],
                           NodeManager::get().mk_value(
                               BitVector::mk_ones(node[0].type().bv_size()))}

  );
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REDOR_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_NOT,
      {rewriter.mk_node(Kind::BV_COMP,
                        {node[0],
                         NodeManager::get().mk_value(
                             BitVector::mk_zero(node[0].type().bv_size()))}

                        )});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REDXOR_ELIM>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  Node result = rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {0, 0});
  for (size_t i = 1, size = node[0].type().bv_size(); i < size; ++i)
  {
    const Node& extract = rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {i, i});
    result              = rewriter.mk_node(Kind::BV_XOR, {result, extract});
  }
  return result;
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_REPEAT_ELIM>::_apply(Rewriter& rewriter,
                                                     const Node& node)
{
  Node result = node[0];
  for (size_t i = 1, repeat = node.index(0); i < repeat; ++i)
  {
    result = rewriter.mk_node(Kind::BV_CONCAT, {result, node[0]});
  }
  return result;
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ROL_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  size_t size = node.type().bv_size();

  if (size == 1)
  {
    return node[0];
  }

  NodeManager& nm       = NodeManager::get();
  Node num_bits         = nm.mk_value(BitVector(size, size));
  const Node& bits_left = rewriter.mk_node(Kind::BV_UREM, {node[1], num_bits});
  const Node& bits_right =
      rewriter.mk_node(Kind::BV_SUB, {num_bits, bits_left});
  const Node& rol =
      rewriter.mk_node(Kind::BV_OR,
                       {rewriter.mk_node(Kind::BV_SHL, {node[0], bits_left}),
                        rewriter.mk_node(Kind::BV_SHR, {node[0], bits_right})});

  // Check if we have to rotate (num_bits > 0)
  return rewriter.mk_node(
      Kind::ITE,
      {rewriter.mk_node(Kind::EQUAL,
                        {num_bits, nm.mk_value(BitVector::mk_zero(size))}),
       node[0],
       rol});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ROLI_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t rotate_by = node.index(0);
  if (rotate_by)
  {
    uint64_t size = node.type().bv_size();
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {rewriter.mk_node(
             Kind::BV_EXTRACT, {node[0]}, {size - rotate_by - 1, 0}),
         rewriter.mk_node(
             Kind::BV_EXTRACT, {node[0]}, {size - 1, size - rotate_by})});
  }
  return node[0];
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ROR_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  size_t size = node.type().bv_size();

  if (size == 1)
  {
    return node[0];
  }

  NodeManager& nm        = NodeManager::get();
  Node num_bits          = nm.mk_value(BitVector(size, size));
  const Node& bits_right = rewriter.mk_node(Kind::BV_UREM, {node[1], num_bits});
  const Node& bits_left =
      rewriter.mk_node(Kind::BV_SUB, {num_bits, bits_right});
  const Node& rol =
      rewriter.mk_node(Kind::BV_OR,
                       {rewriter.mk_node(Kind::BV_SHL, {node[0], bits_left}),
                        rewriter.mk_node(Kind::BV_SHR, {node[0], bits_right})});

  // Check if we have to rotate (num_bits > 0)
  return rewriter.mk_node(
      Kind::ITE,
      {rewriter.mk_node(Kind::EQUAL,
                        {num_bits, nm.mk_value(BitVector::mk_zero(size))}),
       node[0],
       rol});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_RORI_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t rotate_by = node.index(0);
  if (rotate_by)
  {
    uint64_t size = node.type().bv_size();
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {rotate_by - 1, 0}),
         rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, rotate_by})});
  }
  return node[0];
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SADDO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  uint64_t size = node.type().bv_size();
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});
  const Node& add = rewriter.mk_node(Kind::BV_ADD, {node[0], node[1]});
  const Node& sign_add =
      rewriter.mk_node(Kind::BV_EXTRACT, {add}, {size - 1, size - 1});

  // Overflow occurs if
  //  1) negative + negative = positive
  //  2) positive + positive = negative
  Node one  = NodeManager::get().mk_value(BitVector::mk_one(1));
  Node zero = NodeManager::get().mk_value(BitVector::mk_zero(1));
  const Node& both_neg =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, one})});
  const Node& both_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero})});
  const Node& result_neg = rewriter.mk_node(Kind::EQUAL, {sign_add, one});
  const Node& result_pos = rewriter.mk_node(Kind::EQUAL, {sign_add, zero});

  return rewriter.mk_node(
      Kind::OR,
      {rewriter.mk_node(Kind::AND, {both_neg, result_pos}),
       rewriter.mk_node(Kind::AND, {both_pos, result_neg})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SDIV_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size = node.type().bv_size();

  if (size == 1)
  {
    return rewriter.mk_node(
        Kind::BV_NOT, {rewriter.mk_node(Kind::BV_NOT, {node[0]}), node[1]});
  }

  // Extract MSB of operands
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});

  // Checks whether result must be signed
  const Node& negate_res = rewriter.mk_node(Kind::BV_XOR, {sign0, sign1});

  // Normalize operands to unsigned
  Node one = NodeManager::get().mk_value(BitVector::mk_one(1));
  const Node& abs0 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[0]}),
                        node[0]});
  const Node& abs1 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign1, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[1]}),
                        node[1]});

  // Unsigned divison
  const Node& udiv = rewriter.mk_node(Kind::BV_UDIV, {abs0, abs1});

  // Negate result if necessary
  return rewriter.mk_node(Kind::ITE,
                          {rewriter.mk_node(Kind::EQUAL, {negate_res, one}),
                           rewriter.mk_node(Kind::BV_NEG, {udiv}),
                           udiv});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SDIVO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  // Overflow if node[0] = min_signed and node[1] = -1
  uint64_t size   = node.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node min_signed = nm.mk_value(BitVector::mk_min_signed(size));
  Node ones       = nm.mk_value(BitVector::mk_ones(size));
  return rewriter.mk_node(Kind::AND,
                          {rewriter.mk_node(Kind::EQUAL, {node[0], min_signed}),
                           rewriter.mk_node(Kind::EQUAL, {node[1], ones})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SGE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_SLT, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SGT_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_SLT, {node[1], node[0]});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SIGN_EXTEND_ELIM>::_apply(Rewriter& rewriter,
                                                          const Node& node)
{
  uint64_t extend_by = node.index(0);
  if (extend_by)
  {
    NodeManager& nm = NodeManager::get();
    Node zero       = nm.mk_value(BitVector::mk_zero(extend_by));
    Node ones       = nm.mk_value(BitVector::mk_ones(extend_by));
    uint64_t size   = node[0].type().bv_size();
    const Node& sign_bit =
        rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
    return rewriter.mk_node(
        Kind::BV_CONCAT,
        {rewriter.mk_node(
             Kind::ITE,
             {rewriter.mk_node(Kind::EQUAL,
                               {sign_bit, nm.mk_value(BitVector::mk_one(1))}),
              ones,
              zero}),
         node[0]});
  }
  return node[0];
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SLE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_SLT, {node[1], node[0]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SMOD_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size   = node.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(1));
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});
  // Normalize operands to unsigned
  const Node& abs0 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[0]}),
                        node[0]});
  const Node& abs1 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign1, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[1]}),
                        node[1]});
  // Unsigned division
  const Node& urem         = rewriter.mk_node(Kind::BV_UREM, {abs0, abs1});
  const Node& urem_is_zero = rewriter.mk_node(
      Kind::EQUAL, {urem, nm.mk_value(BitVector::mk_zero(size))});
  const Node& neg_urem = rewriter.mk_node(Kind::BV_NEG, {urem});

  // Compute result based on MSB of operands
  Node zero1 = nm.mk_value(BitVector::mk_zero(1));
  const Node& both_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero1}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero1})});
  const Node& neg_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero1})});
  const Node& pos_neg =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero1}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, one})});

  return rewriter.mk_node(
      Kind::ITE,
      {rewriter.mk_node(Kind::OR, {urem_is_zero, both_pos}),
       urem,
       rewriter.mk_node(
           Kind::ITE,
           {neg_pos,
            rewriter.mk_node(Kind::BV_ADD, {neg_urem, node[1]}),
            rewriter.mk_node(Kind::ITE,
                             {pos_neg,
                              rewriter.mk_node(Kind::BV_ADD, {urem, node[1]}),
                              neg_urem})})});
}

// template <>
// Node
// RewriteRule<RewriteRuleKind::BV_SMULO_ELIM>::_apply(Rewriter& rewriter,
//                                                     const Node& node)
//{
//   uint64_t size = node.type().bv_size();
//
//   NodeManager& nm = NodeManager::get();
//   if (size == 1)
//   {
//     Node one = nm.mk_value(BitVector::mk_one(1));
//     return rewriter.mk_node(Kind::AND,
//                             {rewriter.mk_node(Kind::EQUAL, {node[0], one}),
//                              rewriter.mk_node(Kind::EQUAL, {node[1], one})});
//   }
//
//   if (size == 2)
//   {
//     // TODO:
//
//   }
// }

template <>
Node
RewriteRule<RewriteRuleKind::BV_SREM_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  uint64_t size = node.type().bv_size();

  if (size == 1)
  {
    return rewriter.mk_node(
        Kind::BV_AND, {node[0], rewriter.mk_node(Kind::BV_NOT, {node[1]})});
  }

  NodeManager& nm = NodeManager::get();

  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});

  // Normalize operands to unsigned
  Node one = nm.mk_value(BitVector::mk_one(1));
  const Node& abs0 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[0]}),
                        node[0]});
  const Node& abs1 =
      rewriter.mk_node(Kind::ITE,
                       {rewriter.mk_node(Kind::EQUAL, {sign1, one}),
                        rewriter.mk_node(Kind::BV_NEG, {node[1]}),
                        node[1]});

  const Node& urem     = rewriter.mk_node(Kind::BV_UREM, {abs0, abs1});
  const Node& neg_urem = rewriter.mk_node(Kind::BV_NEG, {urem});
  return rewriter.mk_node(
      Kind::ITE, {rewriter.mk_node(Kind::EQUAL, {sign0, one}), neg_urem, urem});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SSUBO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  uint64_t size = node.type().bv_size();
  const Node& sign0 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[0]}, {size - 1, size - 1});
  const Node& sign1 =
      rewriter.mk_node(Kind::BV_EXTRACT, {node[1]}, {size - 1, size - 1});
  const Node& sub = rewriter.mk_node(Kind::BV_SUB, {node[0], node[1]});
  const Node& sign_sub =
      rewriter.mk_node(Kind::BV_EXTRACT, {sub}, {size - 1, size - 1});

  // Overflow occurs if
  //  1) negative - positive = positive
  //  2) postive - negative = negative
  Node one  = NodeManager::get().mk_value(BitVector::mk_one(1));
  Node zero = NodeManager::get().mk_value(BitVector::mk_zero(1));
  const Node& neg_pos =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, one}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, zero})});
  const Node& pos_neg =
      rewriter.mk_node(Kind::AND,
                       {rewriter.mk_node(Kind::EQUAL, {sign0, zero}),
                        rewriter.mk_node(Kind::EQUAL, {sign1, one})});
  const Node& result_neg = rewriter.mk_node(Kind::EQUAL, {sign_sub, one});
  const Node& result_pos = rewriter.mk_node(Kind::EQUAL, {sign_sub, zero});

  return rewriter.mk_node(Kind::OR,
                          {rewriter.mk_node(Kind::AND, {neg_pos, result_pos}),
                           rewriter.mk_node(Kind::AND, {pos_neg, result_neg})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_SUB_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_ADD,
                          {node[0], rewriter.mk_node(Kind::BV_NEG, {node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_UADDO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  const Node& add = rewriter.mk_node(
      Kind::BV_ADD,
      {rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[0]}, {1}),
       rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[1]}, {1})});
  uint64_t size = add.type().bv_size();
  Node one      = NodeManager::get().mk_value(BitVector::mk_one(1));
  return rewriter.mk_node(
      Kind::EQUAL,
      {rewriter.mk_node(Kind::BV_EXTRACT, {add}, {size - 1, size - 1}), one});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_UGE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_ULT, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_UGT_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::BV_ULT, {node[1], node[0]});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ULE_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(Kind::NOT,
                          {rewriter.mk_node(Kind::BV_ULT, {node[1], node[0]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_USUBO_ELIM>::_apply(Rewriter& rewriter,
                                                    const Node& node)
{
  const Node& sub = rewriter.mk_node(
      Kind::BV_SUB,
      {rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[0]}, {1}),
       rewriter.mk_node(Kind::BV_ZERO_EXTEND, {node[1]}, {1})});
  uint64_t size = sub.type().bv_size();
  Node one      = NodeManager::get().mk_value(BitVector::mk_one(1));
  return rewriter.mk_node(
      Kind::EQUAL,
      {rewriter.mk_node(Kind::BV_EXTRACT, {sub}, {size - 1, size - 1}), one});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node)
{
  return rewriter.mk_node(Kind::BV_NOT,
                          {rewriter.mk_node(Kind::BV_XOR, {node[0], node[1]})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_XOR_ELIM>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  return rewriter.mk_node(
      Kind::BV_AND,
      {rewriter.mk_node(Kind::BV_OR, {node[0], node[1]}),
       rewriter.mk_node(Kind::BV_NOT,
                        {rewriter.mk_node(Kind::BV_AND, {node[0], node[1]})})});
}

template <>
Node
RewriteRule<RewriteRuleKind::BV_ZERO_EXTEND_ELIM>::_apply(Rewriter& rewriter,
                                                          const Node& node)
{
  uint64_t extend_by = node.index(0);
  if (extend_by)
  {
    Node zero = NodeManager::get().mk_value(BitVector::mk_zero(extend_by));
    return rewriter.mk_node(Kind::BV_CONCAT, {zero, node[0]});
  }
  return node[0];
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla
