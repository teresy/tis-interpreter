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

#ifndef __FC_CTYPE
#define __FC_CTYPE
#include "features.h"

/* ISO C : 7.4.1 */

__BEGIN_DECLS

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isalnum(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isalpha(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isblank(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int iscntrl(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isdigit(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isgraph(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int islower(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isprint(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int ispunct(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isspace(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isupper(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isxdigit(int c);

/* ISO C : 7.4.2 */

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int tolower(int c);

/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int toupper(int c);

/* POSIX */
/*@ requires -1 <= c <= 255;
    assigns \result \from c ; */
int isascii(int c);

__END_DECLS

#endif
