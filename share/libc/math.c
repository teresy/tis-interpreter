/* ISO C: 7.12 */

#include "math.h"

double fabs(double x){
  if(x==0.0) return 0.0;
  if (x>0.0) return x;
  return -x;
}

