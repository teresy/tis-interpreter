#define _GNU_SOURCE
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "__fc_builtin.h"


unsigned int getpid(void)
{
  return 42;
}

void empty_handler(int i) {}
void (*signal(int signum, void (*handler)(int)  ))(int)
{
    return empty_handler;
}


/* STRING FUNCTIONS */

// from string.c
int char_equal_ignore_case(char c1, char c2);

// Should be in strings.h + strings.c:
/*@ assigns \result \from s1[0 .. n-1], s2[0 ..n-1]; */
int strncasecmp (const char *s1, const char *s2, size_t n) {
  for ( ; n != 0 && *s1 && *s2; n--, s1++, s2++) {
    int res = char_equal_ignore_case(*s1,*s2);
    if(res != 0) return res;
  }
  return 0;
}

void exit(int status) {
}

int vfprintf(FILE *stream, const char *format, va_list ap)
{
    Frama_C_show_each_vfprintf(stream, format, ap);
    return 0;
}

void abort(void)
{
    /*@ assert \false; */
    return;
}

int atoi(const char *nptr) {
  return (int)strtol(nptr, (char **)NULL, 10);
}

/*@ assigns \nothing; // wrong, obviously */
int sscanf(const char *s, const char *fmt, ...);

int puts(const char *s)
{
  return printf("%s\n", s);
}

int fputs(const char *s, FILE *stream)
{
  extern FILE __fc_initial_stdout;
  if (stream == &__fc_initial_stdout)
    return printf("%s", s);
  extern FILE __fc_initial_stderr;
  if (stream == &__fc_initial_stdout)
    return fprintf(stderr, "%s", s);
  return fprintf(stream, "%s", s);
}
