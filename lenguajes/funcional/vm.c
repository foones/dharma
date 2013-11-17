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

#define READ_UINT64(I, J, N) { \
	for (J = I; J < I + sizeof(uint64); J++) { \
		printf("%u\n", sc->code[(J)]); \
		(N) = ((N) << NBITS_PER_BYTE) | sc->code[J]; \
	} \
	I = J; \
}

Fu_Object *fu_vm_execute(Fu_MM *mm, Fu_VMEnvironment *env, uint idx, uint nargs, Fu_Object *args)
/*
 * Execute the code in a supercombinator and build the tree.
 * TODO: add the arguments.
 */
{
	int i, j;
	Fu_VMSupercombinator *sc = env->defs[idx];
	assert(sc->nargs == 0);

	Fu_Object **stack;
	uint stack_capacity;
	uint stack_index;

	DEF_STACK(stack);

	for (i = 0; i < sc->code_len;) {
		switch (sc->code[i]) {
		case FU_OP_PUSH_CONS:
			{
			uint64 constructor_id;
			i++;
			READ_UINT64(i, j, constructor_id);

			Fu_Object *constructor = fu_dict_get(&env->constructors, constructor_id);
			if (constructor == NULL) {
				constructor = fu_constructor(mm, constructor_id);
				fu_dict_define(&env->constructors, constructor_id, constructor);
			}
			printf("pushing constructor: %llu\n", constructor_id);
			STACK_PUSH(stack, constructor);
			break;
			}
		case FU_OP_PUSH_COMB:
			{
			uint64 supercombinator = 0;
			i++;
			READ_UINT64(i, j, supercombinator);
			printf("pushing supercombinator: %llu\n", supercombinator);
			/*STACK_PUSH(stack, fu_supercombinator(mm, supercombinator));*/
			break;
			}
		}
	}
	return STACK_TOP(stack);
}

