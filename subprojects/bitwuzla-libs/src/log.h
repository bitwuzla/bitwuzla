#ifndef BZLALS__LOG_H
#define BZLALS__LOG_H

#define BZLALSLOGLEVEL 1

#include <iosfwd>
class OstreamVoider
{
 public:
  OstreamVoider() = default;
  void operator&(std::ostream& ostream) { (void) ostream; }
};

#define BZLALSLOG BZLALSLOGLEVEL == 0 ? (void) 0 : OstreamVoider() & std::cout

#endif
