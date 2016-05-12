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
    char* ret=0;
    do {
        if( *s == (char)c )
            ret=s;
    } while(*s++);
    return ret;
}

char *strstr(const char *string, const char *substring)
{
    char *a, *b;
    
    /* First scan quickly through the two strings looking for a
     * single-character match.  When it's found, then compare the
     * rest of the substring.
     */

    b = substring;
    if (*b == 0) {
	return string;
    }
    for ( ; *string != 0; string += 1) {
	if (*string != *b) {
	    continue;
	}
	a = string;
	while (1) {
	    if (*b == 0) {
		return string;
	    }
	    if (*a++ != *b++) {
		break;
	    }
	}
	b = substring;
    }
    return (char *) 0;
}

char* strncat(char *dest, const char *src, size_t n)
{
  size_t dest_len = strlen(dest);
  size_t i;

  for (i = 0 ; i < n && src[i] != '\0' ; i++)
    dest[dest_len + i] = src[i];
  dest[dest_len + i] = '\0';

  return dest;
}

char *strerror(int errnum)
{
  return "strerror message by tis-interpreter";
}

int strcasecmp(const char *s1, const char *s2)
{
  while(*s1 && *s2) {
    unsigned char c1 = *s1;
    c1 += ( c1 >= 'A' & c1 <= 'Z') << 5;
    unsigned char c2 = *s2;
    c2 += ( c2 >= 'A' & c2 <= 'Z') << 5;
    int res = c2 - c1;
    if(res != 0) return res;
    s1++;
    s2++;
  }

  if( *s1 == 0 && *s2 == 0) return 0;
  if( *s1 == 0) return -1;
  return 1;
}
