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

void *memchr(const void *s, int c, size_t n) {
  unsigned char cc = (unsigned char) c;
  const unsigned char * p = s;
  for (int i = n; i > 0; i--, p++) {
    if (*p == cc) return (void*) p;
  }
  return NULL;
}

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

#ifndef TIS_MKFS
size_t fwrite(const void *ptr, size_t size, size_t nmemb,
                     FILE *stream) {
  return nmemb;
}
int puts(const char *s) {
  return printf ("TIS puts: %s", s);
}
int fputs(const char *s, FILE *stream) {
  return printf ("TIS fputs: %s", s);
}

int putc (int c, FILE *stream) {
  printf ("TIS putc: %c", c);
  return (unsigned char) c;
}

int fflush(FILE *stream) {
  return 0;
}
#endif

void exit(int status) {
}

int vfprintf(FILE *stream, const char *format, va_list ap)
{
    Frama_C_show_each_vfprintf(stream, format, ap);
    return 0;
}

/*@ assigns __fc_heap_status \from fmt[..], __fc_heap_status; */
int asprintf(char **dest, const char *fmt, ...)
{
  char *res = malloc(80);
  *dest = res;
  Frama_C_make_unknown(res, 79);
  res[79] = 0;
  return 79;
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
int sscanf(const char *s, const char *fmt, ...)
{
  Frama_C_show_each_sscanf(s, fmt);
  return 0;  
}
