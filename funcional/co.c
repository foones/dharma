#include <stdio.h>

#include "mm.h"

/* Test: cons */

void cons_ref_iterator(MM *mm, MMObject *cons_cell, MMRefCallback callback)
{
	MMObject *car = ((MMObject **)cons_cell->data)[0];
	MMObject *cdr = ((MMObject **)cons_cell->data)[1];
	callback(mm, car);
	callback(mm, cdr);
}

MMTag cons_cell_tag = { cons_ref_iterator };

MMObject *mk_cons_cell(MM *mm, MMObject *car, MMObject *cdr)
{
	MMObject *cons_cell = mm_allocate(mm, &cons_cell_tag, 2 * sizeof(MMObject *));
	((MMObject **)cons_cell->data)[0] = car;
	((MMObject **)cons_cell->data)[1] = cdr;
	return cons_cell;
}

int main()
{
	MM _mm;
	MM *mm = &_mm;
	int i;
	MMObject *lst;

	mm_init(mm);
	mm->root = mk_cons_cell(mm, NULL, NULL);

	lst = NULL;

	for (i = 0; i < 1000000; i++) {
		/*if (i % 1000000 == 0) printf("%u\n", i / 1000000);*/
		if (i % 3 == 0) {
			lst = mk_cons_cell(mm, lst, lst);
			mm->root = lst;
		} else {
			mk_cons_cell(mm, lst, lst);
		}
		/*printf("nalloc: %llu gc_threshold: %llu\n", mm->nalloc, mm->gc_threshold);*/
	}
	mm_end(mm);

	return 0;
}

