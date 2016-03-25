/**************************************************************************/
/*                                                                        */
/*  This file is part of TrustInSoft Analyzer.                            */
/*                                                                        */
/*  Copyright (C) 2013-2014                                               */
/*    TrustInSoft                                                         */
/*                                                                        */
/*  All rights reserved.                                                  */
/*                                                                        */
/**************************************************************************/

/* This file provides intrinsics for SSE. */

#ifndef __FC_XMMINTRIN_H_INCLUDED
#define __FC_XMMINTRIN_H_INCLUDED

#ifndef __SSE__
# error "SSE instruction set not enabled"
#else

extern void
_mm_pause (void)
{
  return;
}

extern inline void
_mm_sfence (void)
{
  __builtin_ia32_sfence ();
}

#endif /* __SSE__ */
#endif
