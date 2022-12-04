#ifndef BZLA_UTIL_OSTREAM_VOIDER_H_INCLUDED
#define BZLA_UTIL_OSTREAM_VOIDER_H_INCLUDED

#include <ostream>

namespace bzla::util {

class OstreamVoider
{
 public:
  OstreamVoider() = default;
  void operator&(std::ostream &ostream) { (void) ostream; }
};

}

#endif
