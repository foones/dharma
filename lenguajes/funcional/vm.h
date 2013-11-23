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
	uint nparams;
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
#define Fu_OP_PUSH_CONS_64	0x14
#define Fu_OP_PUSH_COMB_64	0x24
#define Fu_OP_PUSH_ARG_8	0x31
#define Fu_OP_APP		0x40

#define Fu_VM_TAG_CONSTRUCTOR		0x1
#define Fu_VM_TAG_SUPERCOMBINATOR	0x2
#define Fu_VM_MK_CONSTRUCTOR(ID)	Fu_MM_MK_IMMEDIATE((ID), Fu_VM_TAG_CONSTRUCTOR)
#define Fu_VM_MK_SUPERCOMBINATOR(ID)	Fu_MM_MK_IMMEDIATE((ID), Fu_VM_TAG_SUPERCOMBINATOR)

#define Fu_VM_MAX_ARGS		256

typedef struct _Fu_VM_Environment {
	/* Definition of supercombinators */
	uint ndefs;
	Fu_VMSupercombinator *defs[];
} Fu_VMEnvironment;

typedef struct _Fu_VM {
	Fu_MM mm;			/* Memory manager */
	pthread_t mm_thread;

	Fu_VMEnvironment *env;		/* Definitions of supercombinators */
	
	int nargs;			/* Arguments passed to a supercombinator */
	Fu_Object *args[Fu_VM_MAX_ARGS];

	Fu_Object **stack;		/* Stack of values */
	uint stack_capacity;
	uint stack_index;

	Fu_Object ***spine;		/* Spine */
	uint spine_capacity;
	uint spine_index;
} Fu_VM;

/* For the Fu_Object wrapper */

extern Fu_MMTag fu_vm_tag;

#define Fu_IS_VM(X)		Fu_MM_IS_OF_TYPE(X, fu_vm_tag)
#define Fu_OBJ_AS_VM(X)		Fu_MM_OBJ_AS_OF_TYPE(X, Fu_VM)

/* Functions */

Fu_Object *fu_vm(void);
void fu_vm_end(Fu_Object *vmobj);
Fu_Object *fu_vm_execute(Fu_Object *vmobj, uint supercombinator_id);
void fu_vm_weak_head_normalize(Fu_Object *vmobj, Fu_Object **obj);

void fu_vm_print_object(FILE *out, Fu_Object *obj);

#endif
