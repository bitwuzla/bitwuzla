#ifndef BZLA_TERMINATOR_H_INCLUDED
#define BZLA_TERMINATOR_H_INCLUDED

namespace bzla {

class Terminator
{
 public:
  /** Destructor. */
  virtual ~Terminator(){};
  /**
   * Termination function.
   * If terminator has been connected, call to terminate connected
   * Bitwuzla instance.
   * @return True if the associated instance of Bitwuzla has been terminated.
   */
  virtual bool terminate() = 0;
};

}  // namespace bzla

#endif
