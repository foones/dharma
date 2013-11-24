#ifndef _FU_LINKEDLIST_H_
#define _FU_LINKEDLIST_H_

#include "common.h"

typedef struct _Fu_LinkedList {
	/* Doubly linked list*/
	Fu_Object *first;
	Fu_Object *last;
} Fu_LinkedList;

#define Fu_LIST_IS_EMPTY(LST) ((LST)->first == NULL)

#define foreach(X, L)	for (X = (L)->first; X != NULL; X = X->next)

void fu_list_set_empty(Fu_LinkedList *list);

void fu_list_set_copy(Fu_LinkedList *list_dst, Fu_LinkedList *list_src);

void fu_list_remove(Fu_LinkedList *list, Fu_Object *obj);

Fu_Object *fu_list_pop(Fu_LinkedList *list);

void fu_list_add_front(Fu_LinkedList *list, Fu_Object *obj);

void fu_list_concat(Fu_LinkedList *list1, Fu_LinkedList *list2);
	/* Leaves the result in list1.
	 * list2 is invalidated.
	 */

#endif
