#include <string.h>
#include <stdio.h>

int main(int c, char *v[]) {
  printf("%d\n", c);
  char *p = strchr((char[]){1,2,3,4,0}, c);
}
  
