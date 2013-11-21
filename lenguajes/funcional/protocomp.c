#include <string.h>

#include "Fu.h"

#define IS_VARIABLE(X)		(Fu_MM_IS_IMMEDIATE(X) && Fu_MM_IMMEDIATE_TAG(X) == Fu_PROTO_TAG_VARIABLE)
#define IS_LAMBDA_VAR(X)	(Fu_MM_IS_IMMEDIATE(X) && Fu_MM_IMMEDIATE_TAG(X) == Fu_PROTO_TAG_LAMBDA_VAR)

#define VARIABLE_ID(X)		(Fu_MM_IMMEDIATE_VALUE(X))
#define IS_ABSTRACTION(X)	(Fu_IS_CONS(X) && IS_LAMBDA_VAR(Fu_CONS_HEAD(X)))
#define ABSTRACTION_ID(X)	(Fu_MM_IMMEDIATE_VALUE(Fu_CONS_HEAD(X)))
#define ABSTRACTION_BODY(X)	(Fu_CONS_TAIL(X))

typedef struct _supercombinator {
	uint nparams;
	Fu_VMOpcode *code;
	uint code_index;
	uint code_capacity;
} Supercombinator;

void compile_expression(Fu_MM *mm, Fu_Object *exp, Supercombinator *sc)
{
	assert(exp != NULL);

	sc->nparams = 0;
	Fu_Object *params = NULL;
	while (IS_ABSTRACTION(exp)) {
		params = fu_cons(mm, Fu_PROTO_MK_VARIABLE(ABSTRACTION_ID(exp)), params);
		exp = ABSTRACTION_BODY(exp);
		sc->nparams++;
	}

	if (IS_VARIABLE(exp)) {
		int index = 0;
		int found = 0;
		for (Fu_Object *x = params; x != NULL; x = Fu_CONS_TAIL(x), index++) {
			assert(IS_VARIABLE(exp));
			if (Fu_CONS_HEAD(x) == exp) {
				assert(index <= Fu_VM_MAX_ARGS);
				Fu_STACK_PUSH(sc->code, Fu_OP_PUSH_ARG_8);
				Fu_STACK_PUSH(sc->code, (Fu_VMOpcode)index);
				found = 1;
			}
		}
		if (!found) {
			fprintf(stderr, "variable no ligada!!!: %llu (0x%llx)\n", VARIABLE_ID(exp), VARIABLE_ID(exp));
			exit(1);
		}
	} else {
		assert(Fu_MM_IS_REFERENCE(exp));
		assert(!"not implemented");
	}
}

Fu_VM *fu_proto_compile_definition(Fu_MM *mm, Fu_VM *vm, Fu_Object *exp)
/*
 * Compile an expression in proto-Funes into virtual machine
 * code with supercombinators.
 */
{
	Supercombinator _sc, *sc = &_sc;
	Fu_DEF_STACK(sc->code, Fu_VMOpcode);
	compile_expression(mm, exp, sc);

	/* Initialize the VM */
	fu_vm_init(vm);
	vm->env = (Fu_VMEnvironment *)malloc(sizeof(Fu_VMEnvironment) + 1);
	vm->env->ndefs = 1;
	vm->env->defs[0] = (Fu_VMSupercombinator *)malloc(sizeof(Fu_VMSupercombinator *) + sc->code_index);

	vm->env->defs[0]->nparams = sc->nparams;
	memcpy(vm->env->defs[0]->code, sc->code, sizeof(Fu_VMOpcode) * sc->code_index);
	vm->env->defs[0]->code_len = sc->code_index;

	Fu_STACK_FREE(sc->code);
	return vm;
}

