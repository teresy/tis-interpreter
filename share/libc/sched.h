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

/* This file is Linux-specific. */

#ifndef	__FC_SCHED_H
#define	__FC_SCHED_H

#define CPU_SETSIZE 1024

typedef int cpu_set_t;

/*@ assigns *set \from \nothing; */
void CPU_ZERO(cpu_set_t *set);

/*@ assigns *set \from *set, cpu; */
void CPU_SET(int cpu, cpu_set_t *set);

/*@ assigns *set \from *set, cpu; */
void CPU_CLR (int cpu, cpu_set_t *set);

/*@ assigns \result \from cpu, *set; */
int CPU_ISSET (int cpu, const cpu_set_t *set);

#endif
