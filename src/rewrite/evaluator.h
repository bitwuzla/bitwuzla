#include "node/node.h"

namespace bzla {

class Evaluator
{
 public:
  static Node evaluate(node::Kind kind,
                       const std::vector<Node>& values,
                       const std::vector<uint64_t>& indices = {});
};

}  // namespace bzla
