/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2015                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

/* ISO C: 7.20 */
#ifndef __FC_STDLIB
#define __FC_STDLIB
#include "__fc_define_size_t.h"
#include "__fc_define_wchar_t.h"
#include "features.h"

__BEGIN_DECLS

typedef struct __fc_div_t {
  int quot;              /* Quotient.  */
  int rem;               /* Remainder.  */
} div_t;
typedef struct __fc_ldiv_t {
  long int quot;              /* Quotient.  */
  long int rem;               /* Remainder.  */
} ldiv_t;

typedef struct __fc_lldiv_t {
  long long int quot;              /* Quotient.  */
  long long int rem;               /* Remainder.  */
} lldiv_t;

#include "__fc_define_null.h"

/* These could be customizable */
#define EXIT_FAILURE (-1)
#define EXIT_SUCCESS 0

#include "limits.h"

#define RAND_MAX __FC_RAND_MAX
#define MB_CUR_MAX __FC_MB_CUR_MAX

/*@ assigns \result \from __nptr[..] ; */
double atof(const char *__nptr);

/*@ assigns \result \from __nptr[..] ; */
int atoi(const char *__nptr);
/*@ assigns \result \from __nptr[..] ; */
long int atol(const char *__nptr);
/*@ assigns \result \from __nptr[..] ; */
long long int atoll(const char *__nptr);

/*@ assigns \result \from __nptr[..] ; */
long long int atoq(const char *__nptr);

/* See ISO C: 7.20.1.3 to complete these specifications */

/*@ assigns \result \from __nptr[0..];
    assigns *__endptr \from __nptr, __nptr[0..];
*/
double strtod(const char * restrict __nptr,
     char ** restrict __endptr);

/*@ assigns \result \from __nptr[0..];
    assigns *__endptr \from __nptr, __nptr[0..];
*/
float strtof(const char * restrict __nptr,
     char ** restrict __endptr);

/*@ assigns \result \from __nptr[0..];
    assigns *__endptr \from __nptr, __nptr[0..];
*/
long double strtold(const char * restrict __nptr,
     char ** restrict __endptr);

/* TODO: See ISO C 7.20.1.4 to complete these specifications */
/*@ assigns \result \from __nptr[0..], __base;
    assigns *__endptr \from __nptr, __nptr[0..], __base;
*/
long int strtol(
     const char * restrict __nptr,
     char ** restrict __endptr,
     int __base);

/*@ assigns \result \from __nptr[0..], __base;
    assigns *__endptr \from __nptr, __nptr[0..], __base;
*/
long long int strtoll(
     const char * restrict __nptr,
     char ** restrict __endptr,
     int __base);

/*@ assigns \result \from __nptr[0..], __base;
    assigns *__endptr \from __nptr, __nptr[0..], __base;
*/
unsigned long int strtoul(
     const char * restrict __nptr,
     char ** restrict __endptr,
     int __base);

/*@ assigns \result \from __nptr[0..], __base;
    assigns *__endptr \from __nptr, __nptr[0..], __base;
*/
unsigned long long int strtoull(
     const char * restrict __nptr,
     char ** restrict __endptr,
     int __base);

//@ ghost int __fc_random_counter __attribute__((unused)) __attribute__((FRAMA_C_MODEL));
const unsigned long __fc_rand_max = __FC_RAND_MAX;
/* ISO C: 7.20.2 */
/*@ assigns \result \from __fc_random_counter ;
  @ assigns __fc_random_counter \from __fc_random_counter ;
  @ ensures 0 <= \result <= __fc_rand_max ;
*/
int rand(void);

#ifdef _POSIX_C_SOURCE
# if _POSIX_C_SOURCE >= 200112L
/*@ assigns \result \from __fc_random_counter ;
  @ assigns __fc_random_counter \from __fc_random_counter ;
  @ ensures 0 <= \result < 2147483648 ;
*/
long int lrand48 (void);

/*@ assigns __fc_random_counter \from __seed ; */
void srand48 (long int __seed);
# endif
#endif

/*@ assigns __fc_random_counter \from __seed ; */
void srand(unsigned int __seed);

/* ISO C: 7.20.3.1 */
/*@ requires (size_t)(__nmemb * __size) == __nmemb * __size ; */
void *calloc(size_t __nmemb, size_t __size);

/*@ ghost extern int __fc_heap_status __attribute__((FRAMA_C_MODEL)); */

/*@ axiomatic dynamic_allocation {
  @ predicate is_allocable(size_t n) // Can a block of n bytes be allocated?
  @ reads __fc_heap_status;
  @ }
*/

/*@ allocates \result;
  @ assigns __fc_heap_status \from __size, __fc_heap_status;
  @ assigns \result \from __size, __fc_heap_status;
  @ behavior allocation:
  @   assumes is_allocable(__size);
  @   assigns __fc_heap_status \from __size, __fc_heap_status;
  @   assigns \result \from __size, __fc_heap_status;
  @   ensures \fresh(\result,__size);
  @ behavior no_allocation:
  @   assumes !is_allocable(__size);
  @   assigns \result \from \nothing;
  @   allocates \nothing;
  @   ensures \result==\null;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void *malloc(size_t __size);

/*@ frees __p;
  @ assigns  __fc_heap_status \from __fc_heap_status;
  @ behavior deallocation:
  @   assumes  __p!=\null;
  @   requires freeable:\freeable(__p);
  @   assigns  __fc_heap_status \from __fc_heap_status;
  @   ensures  \allocable(__p);
  @ behavior no_deallocation:
  @   assumes  __p==\null;
  @   assigns  \nothing;
  @   frees    \nothing;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void free(void *__p);

#ifdef FRAMA_C_MALLOC_POSITION
#define __FRAMA_C_STRINGIFY(x) #x
#define __FRAMA_C_XSTRINGIFY(x) __FRAMA_C_STRINGIFY(x)
#define FRAMA_C_LOCALIZE_WARNING (" file " __FILE__ " line " __FRAMA_C_XSTRINGIFY(__LINE__))
#define malloc(x) (__Frama_C_malloc_at_pos(x,__FILE__ "_function_" __func__ "_line_" __FRAMA_C_XSTRINGIFY(__LINE__)))
#define free(x) (__Frama_C_free_at_pos(x,FRAMA_C_LOCALIZE_WARNING))
void *__Frama_C_malloc_at_pos(size_t size,const char* file);
void __Frama_C_free_at_pos(void* ptr,const char* pos);
#endif

/*@
   requires __ptr == \null || \freeable(__ptr);
   allocates \result;
   frees     __ptr;
   assigns   __fc_heap_status \from __fc_heap_status;
   assigns   \result \from __size, __ptr, __fc_heap_status;

   behavior alloc:
     assumes   is_allocable(__size);
     allocates \result;
     assigns   \result \from __size, __fc_heap_status;
     ensures   \fresh(\result,__size);

   behavior dealloc:
     assumes   __ptr != \null;
     assumes   is_allocable(__size);
     requires  \freeable(__ptr);
     frees     __ptr;
     ensures   \allocable(__ptr);
     ensures   \result == \null || \freeable(\result);

   behavior fail:
     assumes !is_allocable(__size);
     allocates \nothing;
     frees     \nothing;
     assigns   \result \from __size, __fc_heap_status;
     ensures   \result == \null;

   complete behaviors;
   disjoint behaviors alloc, fail;
   disjoint behaviors dealloc, fail;
  */
void *realloc(void *__ptr, size_t __size);


/* ISO C: 7.20.4 */

/*@ assigns \nothing;
  @ ensures \false; */
void abort(void) __attribute__ ((__noreturn__));

/*@ assigns \result \from \nothing ;*/
int atexit(void (*__func)(void));

/*@ assigns \result \from \nothing ;*/
int at_quick_exit(void (*__func)(void));

/*@
  assigns \nothing;
  ensures \false;
*/
void exit(int __status) __attribute__ ((__noreturn__));

/*@
  assigns \nothing;
  ensures \false;
*/
void _Exit(int __status) __attribute__ ((__noreturn__));

/*@
  assigns \result \from __name;
  ensures \result == \null || \valid(\result) ;
 */
char *getenv(const char *__name);

int putenv(char *__string);

int setenv(const char *__name, const char *__value, int __overwrite);

int unsetenv(const char *__name);

/*@
  assigns \nothing;
  ensures \false; */
void quick_exit(int __status) __attribute__ ((__noreturn__));

/*@ assigns \result \from __string[..]; */
int system(const char *__string);

/* ISO C: 7.20.5 */

/* TODO: use one of the well known specification with high order compare :-) */
/*@  assigns ((char*)\result)[..] \from ((char*)__key)[..], ((char*)__base)[..],
                                        __nmemb, __size, *__compar;  */
void *bsearch(const void *__key, const void *__base,
     size_t __nmemb, size_t __size,
     int (*__compar)(const void *, const void *));

/*@ assigns ((char*)__base)[..] \from ((char*)__base)[..], __nmemb, __size, *__compar ;
 */
  void qsort(void *__base, size_t __nmemb, size_t __size,
             int (*__compar)(const void *, const void *));

/* ISO C: 7.20.6 */

/*@
  requires abs_representable:(int)(-__j) == -__j ;
  assigns \result \from __j ;
*/
int abs(int __j);

/*@
  requires abs_representable:(long)(-__j) == -__j ;
  assigns \result \from __j ; */
long int labs(long int __j);

/*@
  requires abs_representable:(long long)(-__j) == -__j ;
  assigns \result \from __j ; */
long long int llabs(long long int __j);

/*@ assigns \result \from __numer,__denom ; */
div_t div(int __numer, int __denom);
/*@ assigns \result \from __numer,__denom ; */
ldiv_t ldiv(long int __numer, long int __denom);
/*@ assigns \result \from __numer,__denom ; */
lldiv_t lldiv(long long int __numer, long long int __denom);

/* ISO C: 7.20.7 */
/*@ assigns \result \from __s[0..], __n ;*/
int mblen(const char *__s, size_t __n);

/*@ assigns \result, __pwc[0..__n-1] \from __s[0..__n-1], __n ;
*/
int mbtowc(wchar_t * restrict __pwc,
     const char * restrict __s,
     size_t __n);

/*@ assigns \result, __s[0..] \from __wc ; */
int wctomb(char *__s, wchar_t __wc);

/* ISO C: 7.20.8 */

/*@ assigns \result, __pwcs[0..__n-1] \from __s[0..__n-1], __n ; */
size_t mbstowcs(wchar_t * restrict __pwcs,
     const char * restrict __s,
     size_t __n);

/*@ assigns \result, __s[0..__n-1] \from __pwcs[0..__n-1] , __n ; */
size_t wcstombs(char * restrict __s,
     const wchar_t * restrict __pwcs,
     size_t __n);


__END_DECLS

#endif
