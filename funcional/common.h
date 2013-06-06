#ifndef _FU_COMMON_H_
#define _FU_COMMON_H_

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define	Fu_KB	1024
#define	Fu_MB	(1024 * Fu_KB)

#define fu_fail(MSG, ...)	{ fprintf(stderr, MSG, __VA_ARGS__); exit(1); }

typedef unsigned char uchar;
typedef unsigned int uint;

#define TRUE	1
#define FALSE	0

#endif
