#ifndef _FU_COMMON_H_
#define _FU_COMMON_H_

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <pthread.h>

#define	Fu_KB	1024
#define	Fu_MB	(1024 * Fu_KB)

#define fu_fail(MSG, ...)	{ fprintf(stderr, MSG, __VA_ARGS__); exit(1); }

typedef unsigned char uchar;
typedef unsigned int uint;
typedef unsigned long long int uint64;

#define TRUE	1
#define FALSE	0

#define forn(I, N)	for (I = 0; I < (N); I++)

/* Simple growable stack implementation */

#define Fu_MIN_STACK_SIZE	1
#define Fu_DEF_STACK(S) \
	S = (__typeof__(S))malloc(sizeof(__typeof__(*(S))) * Fu_MIN_STACK_SIZE); \
	S##_capacity = Fu_MIN_STACK_SIZE; \
	S##_index = 0;
#define Fu_STACK_GROW(S) { \
	__typeof__(S) __temp = (__typeof__(S))malloc(sizeof(__typeof__(*(S))) * 2 * (S##_capacity)); \
	memcpy(__temp, (S), sizeof(__typeof__(*(S))) * (S##_capacity)); \
	__typeof__(S) __old = (S); \
	(S) = __temp; \
	free(__old); \
	(S##_capacity) *= 2; \
}
#define Fu_STACK_PUSH(S, X) { \
	if ((S##_index) == (S##_capacity)) { \
		Fu_STACK_GROW(S); \
	} \
	(S)[(S##_index)] = (X); \
	(S##_index)++; \
}
#define Fu_STACK_TOP(S) ((S)[(S##_index) - 1])
#define Fu_STACK_POP(S) ((S)[--(S##_index)])
#define Fu_STACK_FREE(S) free(S)

/* Fu_Object is just an alias for Fu_MMObject */
typedef struct _Fu_MMObject Fu_Object;

#endif
