#include "Fu.h"

typedef uchar Fu_VMOpcode;

/*
 * Each supercombinator has a number of parameters
 * and corresponding code.
 */
typedef struct _Fu_VMSupercombinator {
	uint nargs;
	uint code_len;
	Fu_VMOpcode code[];
} Fu_VMSupercombinator;

#define FU_OP_PUSH_IMM	0x01
#define FU_OP_PUSH_COMB	0x02
#define FU_OP_APP	0x03

/*
 * A VM environment is a set of supercombinators, each
 * with an index.
 */
typedef struct _Fu_VMEnvironment {
	/* Definition of supercombinators */
	uint ndefs;
	Fu_VMSupercombinator *defs[];
} Fu_VMEnvironment;

Fu_Object *fu_vm_execute(Fu_VMEnvironment *env, uint idx)
{
	int i;
	Fu_VMSupercombinator *sc = env->defs[idx];
	assert(sc->nargs == 0);

	for (i = 0; i < sc->code_len; i++) {
		switch (sc->code[i]) {
		case FU_OP_PUSH_IMM:
			break;
		}
	}
	return NULL;
}

