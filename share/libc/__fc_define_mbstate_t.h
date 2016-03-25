/**************************************************************************/
/*                                                                        */
/*  This file is part of TrustInSoft Analyzer.                            */
/*                                                                        */
/**************************************************************************/

#ifndef __FC_DEFINE_MBSTATE_T
#define __FC_DEFINE_MBSTATE_T

typedef struct
{
  int __count;
  union
  {
    wint_t __wch;
    char __wchb[4];
  } __value;
} mbstate_t;

#endif
