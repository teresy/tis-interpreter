/**************************/
/********** POSIX *********/
/**************************/

#include <sys/resource.h>

int getrlimit(int r, struct rlimit *rl)
{
  // TODO: these could be more plausible but let's do that when it
  // becomes necessary
  rl->rlim_cur = 100;
  rl->rlim_max = 200;
  return 0;
}

int setrlimit(int r, const struct rlimit *rl)
{
  return 0;
}
