#include "Fu.h"

typedef struct _Cons {
	Fu_Object *car;
	Fu_Object *cdr;
} Cons;

void cons_ref_iterator(Fu_MM *mm, Fu_Object *cons_cell, Fu_MMRefCallback callback)
{
	Fu_Object *car = ((Cons *)cons_cell->data)->car;
	Fu_Object *cdr = ((Cons *)cons_cell->data)->cdr;
	callback(mm, car);
	callback(mm, cdr);
}

Fu_MMTag cons_cell_tag = { cons_ref_iterator };

Fu_Object *fu_cons(Fu_MM *mm, Fu_Object *car, Fu_Object *cdr)
{
	Fu_Object *cons_cell = fu_mm_allocate(mm, &cons_cell_tag, sizeof(Cons));
	((Cons *)cons_cell->data)->car = car;
	((Cons *)cons_cell->data)->cdr = cdr;
	return cons_cell;
}

