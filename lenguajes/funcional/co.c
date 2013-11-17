#include <stdio.h>
#include "Fu.h"

void test_mm()
{
	Fu_MM _mm;
	Fu_MM *mm = &_mm;
	int i;
	Fu_MMObject *lst;

	fu_mm_init(mm);
	mm->root = fu_cons(mm, NULL, NULL);

	lst = NULL;

	for (i = 0; i < 1000000; i++) {
	/*for (i = 0; i < 10000000; i++) {*/
		/*if (i % 1000000 == 0) printf("%u\n", i / 1000000);*/
		if (i % 3 == 0) {
			lst = fu_cons(mm, lst, lst);
			mm->root = lst;
		} else if (i % 3 == 1) {
			lst = fu_cons(mm, lst, Fu_MM_MK_IMMEDIATE(32982, 1));
			mm->root = lst;
		} else {
			fu_cons(mm, lst, lst);
		}
		/*printf("nalloc: %llu gc_threshold: %llu\n", mm->nalloc, mm->gc_threshold);*/
	}
	fu_mm_end(mm);
}

void test_lexer()
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
void test_dict()
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

void test_vm()
{
	Fu_MM _mm;
	Fu_MM *mm = &_mm;

	fu_mm_init(mm);

	int ndefs = 1;
	Fu_VMEnvironment *env = (Fu_VMEnvironment *)malloc(sizeof(Fu_VMEnvironment) + ndefs * sizeof(Fu_VMSupercombinator));

	/* Constructors */
	fu_dict_init(&env->constructors);

	/* Supercombinators */

	env->ndefs = ndefs;

	int d;
	int code_len;

	d = 0;
	code_len = 9;
	env->defs[d] = (Fu_VMSupercombinator *)malloc(sizeof(Fu_VMSupercombinator) + code_len * sizeof(Fu_VMOpcode));
	env->defs[d]->nargs = 0;
	env->defs[d]->code_len = code_len;
	env->defs[d]->code[0] = FU_OP_PUSH_CONS;
	env->defs[d]->code[1] = 0x00;
	env->defs[d]->code[2] = 0x00;
	env->defs[d]->code[3] = 0x00;
	env->defs[d]->code[4] = 0x00;
	env->defs[d]->code[5] = 0x00;
	env->defs[d]->code[6] = 0x00;
	env->defs[d]->code[7] = 0x00;
	env->defs[d]->code[8] = 0x01;

	Fu_Object *res;
	
	res = fu_vm_execute(mm, env, 0, 0, NULL);
	printf("%p\n", res);
	res = fu_vm_execute(mm, env, 0, 0, NULL);
	printf("%p\n", res);
	fu_mm_end(mm);
}

int main()
{
	/*test_mm();*/
	/*test_lexer();*/
	/*test_dict();*/
	test_vm();
	return 0;
}

