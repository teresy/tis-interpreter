/**************************************************************************/
/*                                                                        */
/*  This file is part of TrustInSoft Analyzer.                            */
/*                                                                        */
/*  Copyright (C) 2015                                                    */
/*    TrustInSoft                                                         */
/*                                                                        */
/*  All rights reserved.                                                  */
/*                                                                        */
/**************************************************************************/

#ifndef __FC_DEFINE_GETOPT
#define __FC_DEFINE_GETOPT
#include "features.h"

__BEGIN_DECLS

extern char *optarg;
extern int optind, opterr, optopt;

/*@
  assigns \result, *optarg, optind, opterr, optopt
             \from argc, argv[0..argc-1], optstring[0..];
 */
extern int getopt(int argc, char * const argv[], const char *optstring);

__END_DECLS

#endif
