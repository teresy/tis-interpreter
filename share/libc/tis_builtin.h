/**************************************************************************/
/*                                                                        */
/*  This file is part of TrustInSoft Analyzer.                            */
/*                                                                        */
/*  Copyright (C) 2013-2015                                               */
/*    TrustInSoft                                                         */
/*                                                                        */
/*  All rights reserved.                                                  */
/*                                                                        */
/**************************************************************************/

#ifndef __TIS_BUILTIN_H
#define __TIS_BUILTIN_H

#include "features.h"
#include <__fc_define_size_t.h>

__BEGIN_DECLS

/*@ assigns \nothing; */
void tis_watch_cardinal(void *p, size_t s, int maximal_cardinal, int n);
/*@ assigns \nothing; */
void tis_watch_value(void *p, size_t s, int forbidden_value, int n);
/*@ assigns \nothing; */
void tis_watch_address(void *p, size_t s, int n);
/*@ assigns \nothing; */
void tis_watch_garbled(void *p, size_t s, int n);

/*@ ghost extern int __fc_heap_status __attribute__((FRAMA_C_MODEL)); */
/*@ allocates \result;
  @ assigns __fc_heap_status \from size, __fc_heap_status;
  @ assigns \result \from size, __fc_heap_status;
  @*/
void *tis_alloc_size(size_t size);

/*@ assigns \nothing; */
void tis_variable_split(void *p, size_t s, int limit);

/*@ assigns \result \from p;
  @ ensures \result == \base_addr(p);
*/
void *tis_base_addr(void *p);

/*@ requires n != 0;
  @ requires \valid_read((char *)src1 + (0 .. n - 1));
  @ requires \valid_read((char *)src2 + (0 .. n - 1));
  @ assigns \nothing; */
void tis_check_included(const void *src1, size_t n, const void *src2);

/*@ assigns \nothing; */
void tis_print_subexps(const char *description, ...);

//@ assigns \result \from p, start, end;
int tis_ptr_is_within(void *p, void *start, void *end);

//@ assigns \result \from p1, p2;
int tis_ptr_is_less_than(void *p1, void *p2);

__END_DECLS

#endif /* tis_builtin.h */
