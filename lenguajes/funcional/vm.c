#include <string.h>

#include "Fu.h"
#include "vm.h"

#define MIN_STACK_SIZE	1024
#define DEF_STACK(S)	S = (Fu_Object **)malloc(sizeof(Fu_Object *) * MIN_STACK_SIZE); \
			S##_capacity = MIN_STACK_SIZE; \
			S##_index = 0;
#define STACK_GROW(S) { \
	Fu_Object **__temp = (Fu_Object **)malloc(sizeof(Fu_Object *) * 2 * S##_capacity); \
	memcpy(__temp, S, sizeof(Fu_Object *) * S##_capacity); \
	S = __temp; \
	S##_capacity *= 2; \
}
#define STACK_PUSH(S, X) { \
	if (S##_index == S##_capacity) { \
		STACK_GROW(S); \
	} \
	S[S##_index] = (X); \
	S##_index++; \
}
#define STACK_TOP(S) ((S)[(S##_index) - 1])

#define NBITS_PER_BYTE		8

#define READ_UINT8(I, N) { \
	(N) = sc->code[(I)]; \
	(I) = (I) + 1; \
}

#define READ_UINT64(I, J, N) { \
	(N) = 0; \
	for (J = I; J < I + sizeof(uint64); J++) { \
		(N) = ((N) << NBITS_PER_BYTE) | sc->code[J]; \
	} \
	I = J; \
}

#define TAG_CONSTRUCTOR		0x1
#define TAG_SUPERCOMBINATOR	0x2

Fu_Object *fu_vm_execute(Fu_MM *mm, Fu_VMEnvironment *env, uint idx, Fu_Object **args)
/*
 * Execute the code in a supercombinator and build the tree.
 * TODO: add the arguments.
 */
{
	int i, j;
	Fu_VMSupercombinator *sc = env->defs[idx];

	Fu_Object **stack;
	uint stack_capacity;
	uint stack_index;

	DEF_STACK(stack);

	for (i = 0; i < sc->code_len;) {
		switch (sc->code[i]) {
		case FU_OP_PUSH_CONS_64:
			{
			uint64 constructor_id;
			i++;
			READ_UINT64(i, j, constructor_id);

			Fu_Object *constructor = Fu_MM_MK_IMMEDIATE(constructor_id, TAG_CONSTRUCTOR);
			printf("pushing constructor: %llu\n", constructor_id);
			STACK_PUSH(stack, constructor);
			break;
			}
		case FU_OP_PUSH_COMB_64:
			{
			uint64 supercombinator_id;
			i++;
			READ_UINT64(i, j, supercombinator_id);
			Fu_Object *supercombinator = Fu_MM_MK_IMMEDIATE(supercombinator_id, TAG_SUPERCOMBINATOR);
			printf("pushing supercombinator: %llu\n", supercombinator_id);
			STACK_PUSH(stack, supercombinator);
			break;
			}
		case FU_OP_PUSH_ARG_8:
			{
			uchar arg_id;
			i++;
			READ_UINT8(i, arg_id);
			assert(arg_id < sc->nargs);
			Fu_Object *arg = args[arg_id];
			STACK_PUSH(stack, arg);
			}
		}
	}
	return STACK_TOP(stack);
}

