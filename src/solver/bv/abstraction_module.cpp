#include "solver/bv/abstraction_module.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "solver/bv/abstraction_lemmas.h"

namespace bzla::bv {

using namespace node;

/* --- AbstractionModule public --------------------------------------------- */

AbstractionModule::AbstractionModule(Env& env, SolverState& state)
    : d_logger(env.logger()),
      d_solver_state(state),
      d_abstractions(state.backtrack_mgr()),
      d_active_abstractions(state.backtrack_mgr())
{
  d_lemmas_to_check[Kind::BV_MUL].emplace_back(new LemmaMulZero(state));
  d_lemmas_to_check[Kind::BV_MUL].emplace_back(new LemmaMulOne(state));
  d_lemmas_to_check[Kind::BV_MUL].emplace_back(new LemmaMulIc(state));
  d_lemmas_to_check[Kind::BV_MUL].emplace_back(new LemmaMulNeg(state));
  d_lemmas_to_check[Kind::BV_MUL].emplace_back(new LemmaMulValue(state));
}

AbstractionModule::~AbstractionModule() {}

bool
AbstractionModule::abstract(const Node& node) const
{
  return node.kind() == Kind::BV_MUL && node.type().bv_size() >= 32;
}

void
AbstractionModule::register_abstraction(const Node& node)
{
  auto [it, inserted] = d_abstractions.emplace(node, Node());
  if (inserted)
  {
    Node func       = mul_uf(node);
    NodeManager& nm = NodeManager::get();
    it->second      = nm.mk_node(Kind::APPLY, {func, node[0], node[1]});
    d_solver_state.lemma(nm.mk_node(Kind::EQUAL, {node, it->second}));
    d_active_abstractions.push_back(node);
    Log(1) << "Register abstraction: " << node;
  }
}

void
AbstractionModule::check()
{
  for (const Node& abstr : d_active_abstractions)
  {
    check_abstraction(abstr);
  }
}

/* --- AbstractionModule private -------------------------------------------- */

const Node&
AbstractionModule::get_abstraction(const Node& node)
{
  auto it = d_abstractions.find(node);
  assert(it != d_abstractions.end());
  return it->second;
}

const Node&
AbstractionModule::mul_uf(const Node& node)
{
  assert(node.kind() == Kind::BV_MUL);
  NodeManager& nm     = NodeManager::get();
  Type bvt            = node.type();
  Type t              = nm.mk_fun_type({bvt, bvt, bvt});
  auto [it, inserted] = d_mul_ufs.emplace(t, Node());
  if (inserted)
  {
    std::stringstream ss;
    ss << "bvmul_" << bvt.bv_size();
    it->second = nm.mk_const(t, ss.str());
  }
  return it->second;
}

void
AbstractionModule::check_abstraction(const Node& node)
{
  Log(2) << "Check abstraction: " << node << std::endl;
  auto it = d_lemmas_to_check.find(node.kind());
  assert(it != d_lemmas_to_check.end());
  const auto& to_check = it->second;
  if (node.kind() == Kind::BV_MUL)
  {
    Node val_x = d_solver_state.value(node[0]);
    Node val_s = d_solver_state.value(node[1]);
    Node val_t = d_solver_state.value(node);
    Log(2) << "x: " << val_x;
    Log(2) << "s: " << val_s;
    Log(2) << "t: " << val_t;
    for (const auto& lem : to_check)
    {
      LemmaKind k = lem->kind();
      if (lem->check(val_x, val_s, val_t))
      {
        Log(2) << k << " violated";
        Node lemma = lem->instance(node[0], node[1], node);
        d_solver_state.lemma(lemma);
        break;
      }
      if (lem->check(val_s, val_x, val_t))
      {
        Log(2) << k << " violated";
        Node lemma = lem->instance(node[1], node[0], node);
        d_solver_state.lemma(lemma);
        break;
      }
    }
  }
}

}  // namespace bzla::bv
