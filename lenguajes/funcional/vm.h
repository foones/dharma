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

/*
 * Names of the opcodes indicate the number of bits of
 * the argument (and hence the number of bytes to be read
 * from the bytecode).
 *
 * 0x10 --> push a constructor
 * 0x20 --> push a supercombinator
 * 0x30 --> push an argument
 *
 * 0x01 --> 8 bits
 * 0x02 --> 16 bits
 * 0x03 --> 32 bits
 * 0x04 --> 64 bits
 */
#define FU_OP_PUSH_CONS_64	0x14
#define FU_OP_PUSH_COMB_64	0x24
#define FU_OP_PUSH_ARG_8	0x31
#define FU_OP_APP		0x40

typedef struct _Fu_VMEnvironment {
	/* Definition of supercombinators */
	uint ndefs;
	Fu_VMSupercombinator *defs[];
} Fu_VMEnvironment;

Fu_Object *fu_vm_execute(Fu_MM *mm, Fu_VMEnvironment *env, uint idx, Fu_Object **args);

#endif
