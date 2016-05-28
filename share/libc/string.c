#include "string.h"
#include "stdlib.h"

char *strdup(const char *s)
{
  size_t l = strlen(s) + 1;
  char *p = malloc(l);
  memcpy(p, s, l);
  return p;
}

// stpcpy is POSIX.1-2008
#ifdef _POSIX_C_SOURCE
# if _POSIX_C_SOURCE >= 200809L
char *stpcpy(char * dest, const char * from)
{
  char c;
  while (1) {
    c = *from;
    *dest = c;
    if (!c) break;
    from++;
    dest++;
  }
  return dest;
}
# endif
#endif

size_t strspn(const char *s1, const char *s2)
{
  const char *p = s1, *spanp;
  char c, sc;

cont:
  c = *p;
  spanp = s2;
  while (1) {
    sc = *spanp;
    if (sc == 0) break;
    if (sc == c) { p++; goto cont; }
    spanp++;
  }
  return (p - s1);
}

/*
 * Copy s2 to s1, truncating or null-padding to always copy n bytes
 * return s1
 */
char *
strncpy(char *s1, const char *s2, size_t n)
{
  size_t l = strnlen(s2, n);
  if (l < n) {
    /*@ assert \separated(s1 + (0 .. n-1), s2 + (0 .. l)); */
    memset(s1, 0, n);
  }

  memcpy(s1, s2, l);
  return s1;
}

char *strrchr(const char *s, int c)
{
  int r;
  char* ret = 0;
  c = (char)c;    
  while(1) {
    r = *s;
    if (r == c) ret = s;
    if (!r) break;
    s++;
  }
  return ret;
}

char *strstr(const char *string, const char *substring)
{
  size_t l = strlen(substring);
  int c;
  while (1) {
    c = memcmp(string, substring, l);
    if (!c) break;
    c = *string;
    if (!c) {
      string = 0;
      break;
    }
    string++;
  }
  return string;
}

char* strncat(char *dest, const char *src, size_t n)
{
  size_t dlen = strlen(dest);
  char *w = dest + dlen;
  size_t slen = strlen(src);
  if (slen < n) {
    memcpy(w, src, slen + 1);
  }
  else {
    memcpy(w, src, n);
    /*@ assert \separated(w + slen, src + (0 .. n-1)); */
    w[slen] = '\0';
  }
  return dest;
}

char *strerror(int errnum)
{
  return "strerror message by tis-interpreter";
}

int strcasecmp(const char *s1, const char *s2)
{
  int c1, c2;
  int res;
  while (1) {
    c1 = (unsigned char)*s1;
    c2 = (unsigned char)*s2;
    res = c1 - c2 + 32 * ((c1 >= 'A' & c1 <= 'Z') - (c2 >= 'A' & c2 <= 'Z'));
    if ((!c1) | (res != 0)) break;
    s1++; s2++;
  }
  return res;
}

int strncasecmp (const char *s1, const char *s2, size_t n) {
  int c1, c2;
  int res = 0;
  while (1) {
    if (!n) break;
    c1 = (unsigned char)*s1;
    c2 = (unsigned char)*s2;
    res = c1 - c2 + 32 * ((c1 >= 'A' & c1 <= 'Z') - (c2 >= 'A' & c2 <= 'Z'));
    if ((!c1) | (res != 0)) break;
    n--; s1++; s2++;
  }
  return res;
}

