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

#include "stdio.h"

FILE __fc_initial_stdout = {.__fc_stdio_id=1};
FILE * __fc_stdout = &__fc_initial_stdout;

FILE __fc_initial_stderr = {.__fc_stdio_id=2};
FILE * __fc_stderr = &__fc_initial_stderr;

FILE __fc_initial_stdin = {.__fc_stdio_id=0};
FILE * __fc_stdin = &__fc_initial_stdin;

void perror(const char *__s) {
  printf("%s: some error\n", __s);
}
