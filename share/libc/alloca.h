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

#ifndef __FC_ALLOCA_H
#define __FC_ALLOCA_H

#include "__fc_define_size_t.h"
#include "features.h"

__BEGIN_DECLS

/*@ ghost extern int __fc_heap_status __attribute__((FRAMA_C_MODEL)); */

/*@ 
  @ assigns __fc_heap_status \from size, __fc_heap_status;
  @ assigns \result \from size, __fc_heap_status;
*/
void *alloca(size_t size);

__END_DECLS

#endif
