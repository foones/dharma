#include <string.h>

#include "Fu.h"
#include "vm.h"

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

static void vm_ref_iterator(Fu_MM *mm, Fu_Object *vmobj, Fu_MMRefCallback callback)
/*
 * The objects which the callback is fed here constitute the
 * root set of the garbage collector.
 */
{
	assert(Fu_IS_VM(vmobj));
	Fu_VM *vm = Fu_OBJ_AS_VM(vmobj);

	int i;

	/* Arguments */
	for (i = 0; i < vm->nargs; i++) {
		Fu_Object *obj = vm->args[i];
		callback(mm, obj);

		if (Fu_MM_IS_REFERENCE(obj)) { printf("-- tag 1: %s\n", obj->tag->name); }
	}

	/* Objects in the stack */
	for (i = 0; i < vm->stack_index; i++) {
		Fu_Object *obj = vm->stack[i];
		callback(mm, obj);

		if (Fu_MM_IS_REFERENCE(obj)) { printf("-- tag 2: %s\n", obj->tag->name); }
	}

	/* Root of the spine */
	if (vm->spine_index > 0) {
		Fu_Object *obj = *vm->spine[0];
		callback(mm, obj);

		if (Fu_MM_IS_REFERENCE(obj)) { printf("-- tag 3: %s\n", obj->tag->name); }
	}
}

Fu_MMTag fu_vm_tag = { "vm", vm_ref_iterator };

Fu_Object *fu_vm(void)
/*
 * Initializes the stacks for the virtual machine.
 * It also initializes the memory manager, so that the root
 * set for the garbage collector makes sense.
 */
{
	Fu_Object *vmobj = fu_mm_allocate_unmanaged(&fu_vm_tag, sizeof(Fu_VM));
	Fu_VM *vm = Fu_OBJ_AS_VM(vmobj);

	Fu_MM *mm = &vm->mm;

	fu_mm_init(mm);
	fu_mm_set_gc_root(mm, 0, &vmobj);

	vm->env = NULL;
	vm->nargs = 0;
	Fu_DEF_STACK(vm->stack);
	Fu_DEF_STACK(vm->spine);

	/* Main loop */
	pthread_create(&vm->mm_thread, NULL, fu_mm_mainloop, (void *)mm);

	return vmobj;
}

void fu_vm_end(Fu_Object *vmobj)
{
	assert(Fu_IS_VM(vmobj));
	Fu_VM *vm = Fu_OBJ_AS_VM(vmobj);
	
	Fu_STACK_FREE(vm->stack);
	Fu_STACK_FREE(vm->spine);
	fu_mm_end(&vm->mm);

	void *res = NULL;
	pthread_join(vm->mm_thread, &res);

	free(vmobj);
}

Fu_Object *fu_vm_execute(Fu_Object *vmobj, uint supercombinator_id)
/*
 * Execute the VM code of the given supercombinator,
 * building a tree of applications, supercombinators and constructors
 * as a result.
 */
{
	assert(Fu_IS_VM(vmobj));
	Fu_VM *vm = Fu_OBJ_AS_VM(vmobj);
	Fu_MM *mm = &vm->mm;

	int i, j;
	Fu_VMSupercombinator *sc = vm->env->defs[supercombinator_id];

	vm->stack_index = 0;

	for (i = 0; i < sc->code_len;) {
		switch (sc->code[i]) {
		case Fu_OP_PUSH_CONS_64:
			{
			i++;
			uint64 constructor_id;
			READ_UINT64(i, j, constructor_id);

			Fu_Object *constructor = Fu_VM_MK_CONSTRUCTOR(constructor_id);
			Fu_STACK_PUSH(vm->stack, constructor);
			break;
			}
		case Fu_OP_PUSH_COMB_64:
			{
			i++;
			uint64 supercombinator_id;
			READ_UINT64(i, j, supercombinator_id);
			Fu_Object *supercombinator = Fu_VM_MK_SUPERCOMBINATOR(supercombinator_id);
			Fu_STACK_PUSH(vm->stack, supercombinator);
			break;
			}
		case Fu_OP_PUSH_ARG_8:
			{
			i++;
			uchar arg_id;
			READ_UINT8(i, arg_id);
			assert(arg_id < sc->nparams);
			Fu_Object *arg = vm->args[arg_id];
			Fu_STACK_PUSH(vm->stack, arg);
			break;
			}
		case Fu_OP_APP:
			{
			i++;
			assert(vm->stack_index >= 2);
			Fu_Object *arg = vm->stack[vm->stack_index - 1];
			Fu_Object *fun = vm->stack[vm->stack_index - 2];
			fu_cons(mm, fun, arg, &vm->stack[vm->stack_index - 2]);
			vm->stack_index = vm->stack_index - 1;
			break;
			}
		default:
			assert(!"unknown opcode");
			break;
		}
	}
	assert(vm->stack_index == 1);
	return Fu_STACK_TOP(vm->stack);
}

void fu_vm_print_object(FILE *out, Fu_Object *obj)
/* Print a tree */
{
	if (Fu_MM_IS_IMMEDIATE(obj)) {
		fprintf(out, "<IMM tag=0x%llx value=0x%llx>", Fu_MM_IMMEDIATE_TAG(obj), Fu_MM_IMMEDIATE_VALUE(obj));
	} else if (Fu_IS_CONS(obj)) {
		fprintf(out, "(");
		fu_vm_print_object(out, Fu_CONS_HEAD(obj));
		fprintf(out, " . ");
		fu_vm_print_object(out, Fu_CONS_TAIL(obj));
		fprintf(out, ")");
	} else {
		fprintf(out, "<REF %s %p>", obj->tag->name, obj);
	}
}

#define IS_SUPERCOMBINATOR(X)	(Fu_MM_IS_IMMEDIATE(X) && Fu_MM_IMMEDIATE_TAG(X) == Fu_VM_TAG_SUPERCOMBINATOR)

void fu_vm_weak_head_normalize(Fu_Object *vmobj, Fu_Object **obj)
/*
 * Evaluate a tree made out of:
 * - applications
 * - supercombinators
 * - constructors
 * to WHNF.
 * Requires a pointer to a (Fu_Object *) since evaluation
 * overwrites parts of the graph.
 */
{
	assert(Fu_IS_VM(vmobj));
	Fu_VM *vm = Fu_OBJ_AS_VM(vmobj);
	Fu_MM *mm = &vm->mm;

	/* The spine is a stack of (Fu_Object **) */
	uint nargs = 0;

	assert(vm->spine_index == 0);

	while (1) {
		/* Unwind the spine */
		while (Fu_IS_CONS(*obj)) {
			Fu_STACK_PUSH(vm->spine, obj);
			obj = &Fu_CONS_HEAD(*obj);
			nargs++;
		}

		if (!IS_SUPERCOMBINATOR(*obj)) {
			/*
			 * The leftmost atom is not a supercombinator: already in WHNF
			 */
			return;
		}

		uint supercomb_id = Fu_MM_IMMEDIATE_VALUE(*obj);
		Fu_VMSupercombinator *sc = vm->env->defs[supercomb_id];
		if (nargs < sc->nparams) {
			/* Not enough arguments: already in WHNF */
			return;
		}

		assert(sc->nparams < Fu_VM_MAX_ARGS);

		/* Read arguments from spine */
		Fu_Object **root = obj;
		for (int i = 0; i < sc->nparams; i++) {
			root = Fu_STACK_POP(vm->spine);
			vm->args[i] = Fu_CONS_TAIL(*root);
		}
		vm->nargs = sc->nparams;
		nargs -= sc->nparams;

		/* Call supercombinator */
		Fu_Object *res = fu_vm_execute(vmobj, supercomb_id);
		vm->nargs = 0;

		Fu_Object *parent;
		if (vm->spine_index == 0) {
			parent = NULL;
		} else {
			parent = *vm->spine[vm->spine_index - 1];
		}
		/* Overwrite root with result */
		fu_mm_store(mm, parent, root, res);

		obj = root;
	}
}

