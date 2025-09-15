#include "printer/btor2_printer.h"

#include <set>

#include "backtrack/assertion_stack.h"
#include "printer/exception.h"
#include "util/printer.h"

namespace bzla {

void
Btor2Printer::print_formula(std::ostream& os,
                            const backtrack::AssertionView& assertions)
{
  std::vector<Node> visit;
  std::set<Node> cache;
  std::set<Type> type_cache;

  for (size_t i = 0, n = assertions.size(); i < n; ++i)
  {
    visit.emplace_back(assertions[i]);
  }

  // Collect nodes and types
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      type_cache.insert(cur.type());
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
  }

  // Print sorts
  std::unordered_map<Type, int64_t> type_id;
  int64_t cur_id = 1;
  for (const Type& t : type_cache)
  {
    auto [it, inserted] = type_id.emplace(t, cur_id);
    if (inserted)
    {
      ++cur_id;
    }
    int64_t id = it->second;
    os << id << " sort ";
    if (t.is_bool())
    {
      os << "bitvec 1";
    }
    else if (t.is_bv())
    {
      os << "bitvec " << t.bv_size();
    }
    else if (t.is_array())
    {
      os << "array " << type_id[t.array_index()] << " "
         << type_id[t.array_element()];
    }
    else
    {
      std::string tkind = t.is_fp() ? "fp" : "fun";
      throw printer::Exception("invalid type '" + tkind
                               + "', is not BTOR2 compliant");
    }
    os << std::endl;
  }

  uint8_t bv_format = os.iword(util::set_bv_format::s_stream_index_bv_format);
  if (!bv_format) bv_format = 2;
  assert(bv_format == 2 || bv_format == 10 || bv_format == 16);

  // Print nodes
  std::unordered_map<Node, int64_t> node_id;
  for (const Node& n : cache)
  {
    auto [it, inserted] = node_id.emplace(n, cur_id);
    int64_t tid         = type_id[n.type()];
    if (inserted)
    {
      ++cur_id;
    }
    int64_t id = it->second;
    os << id << " ";

    const char* op = "";
    switch (n.kind())
    {
      case node::Kind::CONSTANT:
        os << "input " << tid;
        if (n.symbol())
        {
          os << " " << n.symbol()->get();
        }
        break;

      case node::Kind::VALUE:
        if (bv_format == 2)
        {
          os << "const ";
        }
        else if (bv_format == 10)
        {
          os << "constd ";
        }
        else
        {
          assert(bv_format == 16);
          os << "consth ";
        }
        os << tid << " " << n.value<BitVector>().str(bv_format);
        break;

      case node::Kind::DISTINCT: op = "neq"; break;

      case node::Kind::EQUAL:
      case node::Kind::BV_COMP: op = "eq"; break;

      case node::Kind::ITE: op = "ite"; break;

      case node::Kind::AND:
      case node::Kind::BV_AND: op = "and"; break;

      case node::Kind::IMPLIES: op = "implies"; break;

      case node::Kind::NOT:
      case node::Kind::BV_NOT: op = "not"; break;

      case node::Kind::OR:
      case node::Kind::BV_OR: op = "or"; break;

      case node::Kind::XOR:
      case node::Kind::BV_XOR: op = "xor"; break;

      case node::Kind::BV_ADD: op = "add"; break;
      case node::Kind::BV_ASHR: op = "sra"; break;
      case node::Kind::BV_CONCAT: op = "concat"; break;
      case node::Kind::BV_DEC: op = "dec"; break;
      case node::Kind::BV_EXTRACT: op = "slice"; break;
      case node::Kind::BV_INC: op = "inc"; break;
      case node::Kind::BV_MUL: op = "mul"; break;
      case node::Kind::BV_NAND: op = "nand"; break;
      case node::Kind::BV_NEG: op = "neg"; break;
      case node::Kind::BV_NEGO: op = "nego"; break;
      case node::Kind::BV_NOR: op = "nor"; break;
      case node::Kind::BV_REDAND: op = "redand"; break;
      case node::Kind::BV_REDOR: op = "redor"; break;
      case node::Kind::BV_REDXOR: op = "redxor"; break;
      case node::Kind::BV_ROL: op = "rol"; break;
      case node::Kind::BV_ROR: op = "ror"; break;
      case node::Kind::BV_SADDO: op = "saddo"; break;
      case node::Kind::BV_SDIV: op = "sdiv"; break;
      case node::Kind::BV_SDIVO: op = "sdivo"; break;
      case node::Kind::BV_SGE: op = "sgte"; break;
      case node::Kind::BV_SGT: op = "sgt"; break;
      case node::Kind::BV_SHL: op = "sll"; break;
      case node::Kind::BV_SHR: op = "srl"; break;
      case node::Kind::BV_SIGN_EXTEND: op = "sext"; break;
      case node::Kind::BV_SLE: op = "slte"; break;
      case node::Kind::BV_SLT: op = "slt"; break;
      case node::Kind::BV_SMOD: op = "smod"; break;
      case node::Kind::BV_SMULO: op = "smulo"; break;
      case node::Kind::BV_SREM: op = "srem"; break;
      case node::Kind::BV_SSUBO: op = "ssubo"; break;
      case node::Kind::BV_SUB: op = "sub"; break;
      case node::Kind::BV_UADDO: op = "uaddo"; break;
      case node::Kind::BV_UDIV: op = "udiv"; break;
      case node::Kind::BV_UGE: op = "ugte"; break;
      case node::Kind::BV_UGT: op = "ugt"; break;
      case node::Kind::BV_ULE: op = "ulte"; break;
      case node::Kind::BV_ULT: op = "ult"; break;
      case node::Kind::BV_UMULO: op = "umulo"; break;
      case node::Kind::BV_UREM: op = "urem"; break;
      case node::Kind::BV_USUBO: op = "usubo"; break;
      case node::Kind::BV_XNOR: op = "xnor"; break;
      case node::Kind::BV_ZERO_EXTEND: op = "uext"; break;

      case node::Kind::SELECT: op = "read"; break;
      case node::Kind::STORE: op = "write"; break;

      default: {
        std::stringstream ss;
        ss << n.kind();
        throw printer::Exception("invalid operator '" + ss.str()
                                 + "', is not BTOR2 compliant");
      }
    }

    if (n.num_children() > 0)
    {
      os << op << " " << tid;
      for (const auto& c : n)
      {
        os << " " << node_id[c];
      }
      for (const auto& i : n.indices())
      {
        os << " " << i;
      }
    }
    os << std::endl;
  }

  // Print constraints
  for (size_t i = 0, n = assertions.size(); i < n; ++i)
  {
    os << cur_id++ << " constraint " << node_id[assertions[i]] << std::endl;
  }
}

void
Btor2Printer::print_formula(std::ostream& os,
                            const std::vector<Node>& assertions)
{
  backtrack::AssertionStack stack;
  for (const Node& assertion : assertions)
  {
    stack.push_back(assertion);
  }
  print_formula(os, stack.view());
}

}  // namespace bzla
