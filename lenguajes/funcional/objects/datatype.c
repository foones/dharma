#include "Fu.h"

typedef struct _Cons {
	Fu_Object *head;
	Fu_Object *tail;
} Cons;

void cons_ref_iterator(Fu_MM *mm, Fu_Object *cons_cell, Fu_MMRefCallback callback)
{
	Fu_Object *head = ((Cons *)cons_cell->data)->head;
	Fu_Object *tail = ((Cons *)cons_cell->data)->tail;
	callback(mm, head);
	callback(mm, tail);
}

Fu_MMTag cons_cell_tag = { cons_ref_iterator };

Fu_Object *fu_cons(Fu_MM *mm, Fu_Object *head, Fu_Object *tail)
{
	Fu_Object *cons_cell = fu_mm_allocate(mm, &cons_cell_tag, sizeof(Cons));
	((Cons *)cons_cell->data)->head = head;
	((Cons *)cons_cell->data)->tail = tail;
	return cons_cell;
}

