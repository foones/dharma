#include <string.h>

#include "Fu.h"
#include "vm.h"

#define MIN_STACK_SIZE	1024
#define DEF_STACK(S, T) \
	S = (T *)malloc(sizeof(T) * MIN_STACK_SIZE); \
	S##_capacity = MIN_STACK_SIZE; \
	S##_index = 0;
#define STACK_GROW(S) { \
	__typeof__(S) __temp = (__typeof__(S))malloc(sizeof(__typeof__(*S)) * 2 * (S##_capacity)); \
	memcpy(__temp, (S), sizeof(__typeof__(*S)) * (S##_capacity)); \
	free(S); \
	(S) = __temp; \
	(S##_capacity) *= 2; \
}
#define STACK_PUSH(S, X) { \
	if ((S##_index) == (S##_capacity)) { \
		STACK_GROW(S); \
	} \
	(S)[(S##_index)] = (X); \
	(S##_index)++; \
}
#define STACK_TOP(S) ((S)[(S##_index) - 1])
#define STACK_POP(S) ((S)[--(S##_index)])

#define NBITS_PER_BYTE		8

#define READ_UINT8(I, N) { \
	(N) = sc->code[(I)]; \
	(I)++; \
}

#define READ_UINT64(I, J, N) { \
	(N) = 0; \
	for (J = I; J < I + sizeof(uint64); J++) { \
		(N) = ((N) << NBITS_PER_BYTE) | sc->code[J]; \
	} \
	I = J; \
}

void fu_vm_init(Fu_VM *vm)
{
	DEF_STACK(vm->stack, Fu_Object *);
}

void fu_vm_end(Fu_VM *vm)
{
	free(vm->stack);
}

Fu_Object *fu_vm_execute(Fu_MM *mm, Fu_VM *vm)
/*
 * Execute the code in a supercombinator and build the tree.
 * TODO: add the arguments.
 */
{
	int i, j;
	Fu_VMSupercombinator *sc = vm->env->defs[vm->current_supercomb];

	vm->stack_index = 0;

	for (i = 0; i < sc->code_len;) {
		switch (sc->code[i]) {
		case Fu_OP_PUSH_CONS_64:
			{
			i++;
			uint64 constructor_id;
			READ_UINT64(i, j, constructor_id);

			Fu_Object *constructor = Fu_VM_MK_CONSTRUCTOR(constructor_id);
			STACK_PUSH(vm->stack, constructor);
			break;
			}
		case Fu_OP_PUSH_COMB_64:
			{
			i++;
			uint64 supercombinator_id;
			READ_UINT64(i, j, supercombinator_id);
			Fu_Object *supercombinator = Fu_VM_MK_SUPERCOMBINATOR(supercombinator_id);
			STACK_PUSH(vm->stack, supercombinator);
			break;
			}
		case Fu_OP_PUSH_ARG_8:
			{
			i++;
			uchar arg_id;
			READ_UINT8(i, arg_id);
			assert(arg_id < sc->nparams);
			Fu_Object *arg = vm->args[arg_id];
			STACK_PUSH(vm->stack, arg);
			break;
			}
		case Fu_OP_APP:
			{
			i++;
			assert(vm->stack_index >= 2);
			Fu_Object *arg = STACK_POP(vm->stack);
			Fu_Object *fun = STACK_POP(vm->stack);
			Fu_Object *app = fu_cons(mm, fun, arg);
			STACK_PUSH(vm->stack, app);
			break;
			}
		}
	}
	return STACK_TOP(vm->stack);
}

void fu_vm_print_object(FILE *out, Fu_Object *obj)
/* Print a tree */
{
	if (Fu_MM_IS_IMMEDIATE(obj)) {
		fprintf(out, "<IMM tag=0x%llx value=0x%llx>", Fu_MM_IMMEDIATE_TAG(obj), Fu_MM_IMMEDIATE_VALUE(obj));
	} else if (Fu_IS_CONS(obj)) {
		int first = 1;
		fprintf(out, "(");
		while (Fu_IS_CONS(obj)) {
			if (!first) {
				fprintf(out, " ");
			}
			first = 0;
			fu_vm_print_object(out, Fu_CONS_HEAD(obj));
			obj = Fu_CONS_TAIL(obj);
		}
		if (obj != NULL) {
			fprintf(out, " . ");
			fu_vm_print_object(out, obj);
		}
		fprintf(out, ")");
	} else {
		fprintf(out, "<REF %p>", obj);
	}
}

#define IS_SUPERCOMBINATOR(X)	(Fu_MM_IS_IMMEDIATE(X) && Fu_MM_IMMEDIATE_TAG(X) == Fu_VM_TAG_SUPERCOMBINATOR)

#define CLEANUP() { \
	free(spine); \
}

void fu_vm_eval(Fu_MM *mm, Fu_VM *vm, Fu_Object **obj)
/*
 * Evaluate a tree to WHNF.
 * Requires a pointer to a (Fu_Object *) since evaluation
 * overwrites parts of the graph.
 */
{
	/* The spine is a stack of (Fu_Object **) */
	Fu_Object ***spine;
	uint spine_capacity;
	uint spine_index;
	DEF_STACK(spine, Fu_Object **);

	/* Unwind the spine */
	uint nargs = 0;
	while (Fu_IS_CONS(*obj)) {
		STACK_PUSH(spine, obj);
		obj = &Fu_CONS_HEAD(*obj);
		nargs++;
	}

	if (IS_SUPERCOMBINATOR(*obj)) {
		uint current_supercomb = Fu_MM_IMMEDIATE_VALUE(*obj);
		Fu_VMSupercombinator *sc = vm->env->defs[current_supercomb];
		if (nargs < sc->nparams) {
			/* Already in WHNF */
			CLEANUP();
			return;
		}

		assert(sc->nparams < Fu_VM_MAX_ARGS);

		/* Read arguments from spine */
		Fu_Object **root = obj;
		vm->current_supercomb = current_supercomb;
		for (int i = 0; i < sc->nparams; i++) {
			root = STACK_POP(spine);
			vm->args[i] = Fu_CONS_HEAD(*root);
		}

		/* Call supercombinator */
		printf("calling %u\n", current_supercomb);
		Fu_Object *res = fu_vm_execute(mm, vm);
		printf("got: "); fu_vm_print_object(stdout, res); printf("\n");

		/* Overwrite root with result */
		*root = res;

	} else {
		assert(!"not implemented");
	}

	CLEANUP();
}

