#ifndef _FU_VM_H_
#define _FU_VM_H_

#include "common.h"
#include "mm.h"

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

#define FU_OP_PUSH_CONS	0x01
#define FU_OP_PUSH_COMB	0x02
#define FU_OP_APP	0x03

typedef struct _Fu_VMEnvironment {
	/* Dictionary of current constructors */
	Fu_Dict constructors;
	/* Definition of supercombinators */
	uint ndefs;
	Fu_VMSupercombinator *defs[];
} Fu_VMEnvironment;

Fu_Object *fu_vm_execute(Fu_MM *mm, Fu_VMEnvironment *env, uint idx, uint nargs, Fu_Object *args);

#endif
