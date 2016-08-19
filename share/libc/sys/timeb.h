/**************************************************************************/
/*                                                                        */
/*  This file is part of tis-interpreter.                                 */
/*  Copyright (C) 2016 TrustInSoft                                        */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  General Public License as published by the Free Software              */
/*  Foundation, version 2.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU General Public License version 2 for more details.                */
/*  (enclosed in the file licences/GPLv2).                                */
/*                                                                        */
/**************************************************************************/

/* POSIX header */

#ifndef __FC_SYS_TIMEB_H__
#define __FC_SYS_TIMEB_H__

#include "../features.h"
#include "../__fc_define_time_t.h"

__BEGIN_DECLS

struct timeb {
  time_t time;
  unsigned short millitm;
  short timezone;
  short dstflag;
};

int ftime(struct timeb *timebuf);

__END_DECLS

#endif
