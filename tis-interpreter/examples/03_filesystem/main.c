#include <stdio.h>
#include <stdlib.h>

int main(void) {
  FILE *in = fopen("input", "r");
  if (!in) {
    printf("Couldn't open input file.\n");
    exit(1);
  }
  char b[100];
  size_t r = fread(b, 1, 100, in);
  printf("%zu bytes read:\n", r);
  for (size_t i = 0; i < r; i++)
    printf("%d\n", b[i]);
}
