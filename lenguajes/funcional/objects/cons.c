#include "Fu.h"

static void cons_ref_iterator(Fu_MM *mm, Fu_Object *obj, Fu_MMRefCallback callback)
{
	assert(Fu_IS_CONS(obj));
	callback(mm, Fu_CONS_HEAD(obj));
	callback(mm, Fu_CONS_TAIL(obj));
}

Fu_MMTag fu_cons_tag = { cons_ref_iterator };

Fu_Object *fu_cons(Fu_MM *mm, Fu_Object *head, Fu_Object *tail)
{
	Fu_Cons cons;
	cons.head = head;
	cons.tail = tail;
	return fu_mm_allocate(mm, &fu_cons_tag, sizeof(Fu_Cons), &cons);
}

