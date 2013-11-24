#include "Fu.h"

void fu_list_set_empty(Fu_LinkedList *list)
{
	list->first = NULL;
	list->last = NULL;
}

void fu_list_set_copy(Fu_LinkedList *list_dst, Fu_LinkedList *list_src)
{
	list_dst->first = list_src->first;
	list_dst->last = list_src->last;
}

void fu_list_remove(Fu_LinkedList *list, Fu_Object *obj)
{
	int xx_prelen = 0, xx_poslen = 0;
	Fu_Object *xx;
	printf("[\n");
	foreach (xx, list) {
		printf("\t%p -- ", xx); fu_vm_print_object(stdout, xx); printf("\n");
		xx_prelen++;
	}
	printf("]\n");
	printf("%p -- ", obj); fu_vm_print_object(stdout, obj); printf("\n");
	printf("%u %u\n", obj->prev == NULL, obj->next == NULL);
	if (obj->prev == NULL && obj->next == NULL) {
		assert(xx_prelen == 1);
	}

	assert(!Fu_LIST_IS_EMPTY(list));
	if (obj->prev == NULL) {
		list->first = obj->next;
	} else {
		obj->prev->next = obj->next;
	}
	if (obj->next == NULL) {
		list->last = obj->prev;
	} else {
		obj->next->prev = obj->prev;
	}
	obj->prev = NULL;
	obj->next = NULL;

	foreach (xx, list) { xx_poslen++; }
	assert(xx_poslen == xx_prelen - 1);
}

Fu_Object *fu_list_pop(Fu_LinkedList *list)
{
	Fu_Object *obj = list->first;

	assert(!Fu_LIST_IS_EMPTY(list));
	fu_list_remove(list, obj);
	return obj;
}

void fu_list_add_front(Fu_LinkedList *list, Fu_Object *obj)
{
	obj->prev = NULL;
	obj->next = list->first;
	if (Fu_LIST_IS_EMPTY(list)) {
		list->last = obj;
	} else {
		list->first->prev = obj;
	}
	list->first = obj;
}

void fu_list_concat(Fu_LinkedList *list1, Fu_LinkedList *list2)
{
	if (Fu_LIST_IS_EMPTY(list1)) {
		list1->first = list2->first;
		list1->last = list2->last;
	} else if (!Fu_LIST_IS_EMPTY(list2)) {
		list2->first->prev = list1->last;
		list1->last->next = list2->first;
		list1->last = list2->last;
	}
}

