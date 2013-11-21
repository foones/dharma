#include <stdio.h>
#include "Fu.h"

void *test_mm_worker(void *mmptr)
{
	Fu_MM *mm = (Fu_MM *)mmptr;
	Fu_MMObject *lst = NULL;
	fu_mm_set_gc_root(mm, 0, &lst);
	for (int i = 0; i < 10000000; i++) {
		/*if (i % 1000000 == 0) printf("%u\n", i / 1000000);*/
		/*
		printf("%u %llu\n", i, mm->nalloc);
		printf("%u %lu **\n", i,
						(2 * i * (sizeof(Fu_MMObject) +
						      sizeof(Fu_Cons)) / 3));
						      */

		if (i % 3 == 0) {
			fu_cons(mm, lst, lst, &lst);
		} else if (i % 3 == 1) {
			fu_cons(mm, lst, Fu_MM_MK_IMMEDIATE(32982, 1), &lst);
		} else {
			Fu_Object *tmp;
			fu_cons(mm, lst, lst, &tmp);
		}
		/*printf("nalloc: %llu gc_threshold: %llu\n", mm->nalloc, mm->gc_threshold);*/
	}
	return NULL;
}

void test_mm(void)
{
	Fu_MM _mm;
	Fu_MM *mm = &_mm;

	fu_mm_init(mm);

	pthread_t worker_thread;
	pthread_create(&worker_thread, NULL, test_mm_worker, (void *)mm);

	pthread_t gc_thread;
	pthread_create(&gc_thread, NULL, fu_mm_mainloop, (void *)mm);

	void *res;
	pthread_join(worker_thread, &res);

	fu_mm_end(mm);
	pthread_join(gc_thread, &res);
}

void test_lexer(void)
{
	FILE *f = fopen("test.txt", "r");
	if (!f) {
		fu_fail("%s", "file test.txt does not exist\n");
	}
	Fu_Stream *stream = fu_stream_from_file("test.txt", f);

	Fu_Lexer *lexer = fu_lexer_from_stream(stream);
	while (TRUE) {
		Fu_Token tok = fu_lexer_next_token(lexer);
		if (tok == Fu_TOK_EOF) break;
		printf("t %u\n", tok);
	}

	fclose(f);
}

#include <stdlib.h>
#include <time.h>
void test_dict(void)
{
#define M	1000
	int i;
	unsigned long long int a[M];
	srand(time(NULL));

	for (i = 0; i < M; i++) {
		a[i] = rand() % 1000;
	}

	Fu_Dict dict;
	fu_dict_init(&dict);
	for (i = 0; i < M; i++) {
		fu_dict_define(&dict, i, (void *)a[i]);
	}
	for (i = 0; i < M; i++) {
		printf("%llu %llu\n", (unsigned long long int)fu_dict_get(&dict, i), a[i]);
	}
	fu_free_dict(&dict);
}

#if 0
void test_vm(void)
{
	Fu_MM _mm; Fu_MM *mm = &_mm;
	fu_mm_init(mm);

	Fu_Object *vmobj = fu_vm(mm);
	Fu_VM *vm = Fu_OBJ_AS_VM(vmobj);

	int ndefs = 3;
	vm->env = (Fu_VMEnvironment *)malloc(sizeof(Fu_VMEnvironment) + ndefs * sizeof(Fu_VMSupercombinator));

	/* Supercombinators */

	vm->env->ndefs = ndefs;

	int d;
	int code_len;

	/* def 0 omitted */

	/* def 1 ==> I */
	d = 1;
	code_len = 2;
	vm->env->defs[d] = (Fu_VMSupercombinator *)malloc(sizeof(Fu_VMSupercombinator) + code_len * sizeof(Fu_VMOpcode));
	vm->env->defs[d]->nparams = 1;
	vm->env->defs[d]->code_len = code_len;
	vm->env->defs[d]->code[0] = Fu_OP_PUSH_ARG_8;
	vm->env->defs[d]->code[1] = 0x00;

	/* def 2 ==> K */
	d = 2;
	code_len = 2;
	vm->env->defs[d] = (Fu_VMSupercombinator *)malloc(sizeof(Fu_VMSupercombinator) + code_len * sizeof(Fu_VMOpcode));
	vm->env->defs[d]->nparams = 2;
	vm->env->defs[d]->code_len = code_len;
	vm->env->defs[d]->code[0] = Fu_OP_PUSH_ARG_8;
	vm->env->defs[d]->code[1] = 0x00;

	/* def 3 ==> S */
	d = 3;
	code_len = 11;
	vm->env->defs[d] = (Fu_VMSupercombinator *)malloc(sizeof(Fu_VMSupercombinator) + code_len * sizeof(Fu_VMOpcode));
	vm->env->defs[d]->nparams = 3;
	vm->env->defs[d]->code_len = code_len;
	vm->env->defs[d]->code[0] = Fu_OP_PUSH_ARG_8;
	vm->env->defs[d]->code[1] = 0x00;
	vm->env->defs[d]->code[2] = Fu_OP_PUSH_ARG_8;
	vm->env->defs[d]->code[3] = 0x02;
	vm->env->defs[d]->code[4] = Fu_OP_APP;
	vm->env->defs[d]->code[5] = Fu_OP_PUSH_ARG_8;
	vm->env->defs[d]->code[6] = 0x01;
	vm->env->defs[d]->code[7] = Fu_OP_PUSH_ARG_8;
	vm->env->defs[d]->code[8] = 0x02;
	vm->env->defs[d]->code[9] = Fu_OP_APP;
	vm->env->defs[d]->code[10] = Fu_OP_APP;

	Fu_Object *I = Fu_VM_MK_SUPERCOMBINATOR(0x1);
	Fu_Object *K = Fu_VM_MK_SUPERCOMBINATOR(0x2);
	Fu_Object *S = Fu_VM_MK_SUPERCOMBINATOR(0x3);

	Fu_Object *res = fu_cons(mm, fu_cons(mm, fu_cons(mm, K, I), S), S);
	printf("tree: "); fu_vm_print_object(stdout, res); printf("\n");
	fu_vm_weak_head_normalize(mm, vmobj, &res);
	printf("tree whnf: "); fu_vm_print_object(stdout, res); printf("\n");

	fu_vm_end(vmobj);
	fu_mm_end(mm);
}
#endif

#if 0
void test_protocomp(void)
{
	Fu_MM _mm; Fu_MM *mm = &_mm;
	fu_mm_init(mm);

	Fu_Object *vmobj = fu_proto_compile_definition(mm,
		Fu_PROTO_MK_ABSTRACTION(mm,
			0x10,
			Fu_PROTO_MK_VARIABLE(0x10)
		)
	);

	Fu_Object *res = fu_cons(mm, Fu_VM_MK_SUPERCOMBINATOR(0), Fu_VM_MK_CONSTRUCTOR(0x42));
	printf("tree: "); fu_vm_print_object(stdout, res); printf("\n");
	fu_vm_weak_head_normalize(mm, vmobj, &res);
	printf("tree whnf: "); fu_vm_print_object(stdout, res); printf("\n");

	fu_vm_end(vmobj);
	fu_mm_end(mm);
}
#endif

int main()
{
	test_mm();
	/*test_lexer();*/
	/*test_dict();*/
	/*test_vm();*/
	/*test_protocomp();*/
	return 0;
}

