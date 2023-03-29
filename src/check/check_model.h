#ifndef BZLA_CHECK_CHECK_MODEL_H_INCLUDED

#include <unordered_map>
#include <vector>

#include "solving_context.h"
#include "util/logger.h"

namespace bzla::check {

class CheckModel
{
 public:
  CheckModel(SolvingContext& ctx);

  bool check();

 private:
  void collect_consts();
  void assert_array_model(SolvingContext& ctx,
                          const Node& input,
                          const Node& value) const;
  void assert_fun_model(SolvingContext& ctx,
                        const Node& input,
                        const Node& value) const;

  SolvingContext& d_ctx;

  std::vector<Node> d_consts;
  std::unordered_map<Node, std::vector<Node>> d_fun_apps;

  util::Logger& d_logger;
};

}  // namespace bzla::check

#endif
