# Check if functions required for time statistics are available.
include(CheckCSourceCompiles)
CHECK_C_SOURCE_COMPILES(
"
#include <sys/resource.h>
#include <sys/time.h>
#include <time.h>
int main ()
{
  struct rusage u;
  (void) getrusage(RUSAGE_SELF, &u);
  struct timespec ts;
  (void) clock_gettime (CLOCK_THREAD_CPUTIME_ID, &ts);
  struct timeval tv;
  (void) gettimeofday (&tv, 0);
  return 0;
}
"
HAVE_TIME_UTILS
)
