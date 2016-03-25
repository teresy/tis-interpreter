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

#include <strings.h>
#include <__fc_define_null.h>

char *
index(const char *s, int c)
{
	while (1) {
		if (*s == c)
			return s;
		if (!*s)
			return NULL;
		s++;
	}
}
