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

#ifndef __TIS_SYS_TIMES_H
#define __TIS_SYS_TIMES_H

#include "../__fc_define_clock_t.h"

struct tms {
    clock_t tms_utime;  /* user time */
    clock_t tms_stime;  /* system time */
    clock_t tms_cutime; /* user time of children */
    clock_t tms_cstime; /* system time of children */
};

clock_t times(struct tms *buf);

#endif /* sys/times.h */
