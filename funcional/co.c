#include <stdio.h>
#include "Fu.h"

int main()
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
		} else {
			fu_cons(mm, lst, lst);
		}
		/*printf("nalloc: %llu gc_threshold: %llu\n", mm->nalloc, mm->gc_threshold);*/
	}
	fu_mm_end(mm);

	return 0;
}

