# Check if signals are available.
include(CheckCSourceCompiles)
CHECK_C_SOURCE_COMPILES(
"
#include <signal.h>
#include <unistd.h>
static void catchsig(int sig) { (void) sig; }
int main ()
{
  alarm (0);
  (void) signal (SIGALRM, catchsig);
  (void) signal (SIGINT, catchsig);
  (void) signal (SIGSEGV, catchsig);
  (void) signal (SIGABRT, catchsig);
  (void) signal (SIGTERM, catchsig);
  (void) signal (SIGBUS, catchsig);
  return 0;
}
"
HAVE_SIGNALS
)
