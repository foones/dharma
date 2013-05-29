#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "mm.h"

/* Helpers */

#define whiten(X)	(X)->flags = MM_FLAGS_SET_COLOR((X)->flags, WHITE(mm))
#define grayen(X)	(X)->flags = MM_FLAGS_SET_COLOR((X)->flags, GRAY(mm))

#define forn(I, N)	for (I = 0; I < (N); i++)
#define foreach(X, L)	for (X = (L); X != NULL; X = X->next)

#define GRAY(mm)	(mm)->graycol
#define WHITE(mm)	(1 - GRAY(mm))

static void list_remove(MMObject **list, MMObject *obj)
{
	if (*list == obj) {
		*list = obj->next;
	}
	if (obj->prev != NULL) {
		obj->prev->next = obj->next;
	}
	if (obj->next != NULL) {
		obj->next->prev = obj->prev;
	}
	obj->prev = NULL;
	obj->next = NULL;
}

static MMObject *list_pop(MMObject **list)
{
	MMObject *obj = *list;
	list_remove(list, obj);
	return obj;
}

static void list_add_front(MMObject **list, MMObject *obj)
{
	obj->prev = NULL;
	obj->next = *list;
	if (*list != NULL) {
		(*list)->prev = obj;
	}
	*list = obj;
}

/* MM functions */

void mm_init(MM *mm)
{
	int i;
	mm->black = NULL;
	mm->gray = NULL;
	mm->white = NULL;
	mm->root = NULL;
	mm->nalloc = 0;
	mm->graycol = 0;
	mm->gc_threshold = MM_FIRST_GC_THRESHOLD;
	forn (i, MM_MAX_FREELIST) {
		mm->freelist[i] = NULL;
	}
}

/*
 * If the allocation of an object would exceed the
 * current GC threshold, trigger GC.
 */
MMObject *mm_allocate(MM *mm, MMTag *tag, MMSize size)
{
	MMSize sz = sizeof(MMObject) + size;

	char reach_gc_threshold = mm->nalloc + sz > mm->gc_threshold;
	/*char freelist_empty = sz < MM_MAX_FREELIST && mm->freelist[sz] == NULL;*/
	if (reach_gc_threshold) {
		mm_gc(mm);
	}

	MMObject *obj;

	/* Get memory for the object */
	if (sz < MM_MAX_FREELIST && mm->freelist[sz] != NULL) {
		obj = list_pop(&mm->freelist[sz]);
	} else {
		obj = (MMObject *)malloc(sz);
	}

	obj->flags = MM_FLAGS(size, GRAY(mm));
	obj->tag = tag;
	obj->prev = NULL;
	list_add_front(&mm->black, obj);
	mm->nalloc += sz;
	return obj;
}

/* Mark all the objects white in O(1) */

static void whiten_all(MM *mm)
{
	mm->graycol = 1 - mm->graycol;
	mm->white = mm->black;
	mm->black = NULL;
}

/* Mark */

static void mark_as_gray(MM *mm, MMObject *referenced)
{
	if (referenced != NULL && MM_FLAGS_COLOR(referenced->flags) == WHITE(mm)) {
		list_remove(&mm->white, referenced);
		grayen(referenced);
		list_add_front(&mm->gray, referenced);
	}
}

static void mark(MM *mm)
{
	assert(mm->root != NULL);
	assert(mm->white == NULL);
	assert(mm->gray == NULL);

	/* Whiten all objects */
	whiten_all(mm);

	/* Set the root gray */
	assert(MM_FLAGS_COLOR(mm->root->flags) == WHITE(mm));
	mark_as_gray(mm, mm->root);

	/* While there are gray nodes */
	while (mm->gray != NULL) {
		/* Blacken the first gray object */
		MMObject *obj = list_pop(&mm->gray);
		assert(MM_FLAGS_COLOR(obj->flags) == GRAY(mm));
		list_add_front(&mm->black, obj);

		/* Grayen the white objects referenced by it */
		obj->tag->ref_iterator(mm, obj, mark_as_gray);
	}
}

static void list_deallocate(MMObject *list)
{
	MMObject *p;
	for (p = list; p != NULL;) {
		MMObject *obj = p;
		p = p->next;
		free(obj);
	}
}

static void list_free(MM *mm, MMObject **list)
{
	MMObject *p;
	for (p = *list; p != NULL;) {
		MMObject *obj = p;
		MMSize sz = sizeof(MMObject) + MM_FLAGS_SIZE(obj->flags);
		p = p->next;
		assert(mm->nalloc >= sz);
		mm->nalloc -= sz;
		if (sz < MM_MAX_FREELIST) {
			list_add_front(&mm->freelist[sz], obj);
		} else {
			free(obj);
		}
	}
	*list = NULL;
}

/* Sweep */

static void sweep(MM *mm)
{
	list_free(mm, &mm->white);
	mm->gc_threshold = MAX(2 * mm->nalloc, MM_FIRST_GC_THRESHOLD);
	assert(mm->black != NULL);
	assert(mm->gray == NULL);
}

/*
 * Sketch of the GC algorithm:
 *
 * Mark:
 *
 * - Invert graycol, so all the objects are now colored white.
 *
 * - By DFS, mark all the reachable objects as gray, and
 *   put them in the <black> list.
 *
 * Sweep:
 *
 * - Free the objects remaining in the <white> list, for
 *   they are unreachable.
 *
 */
void mm_gc(MM *mm)
{
	printf("gc\n");
	mark(mm);
	sweep(mm);
}

/* Free all the remaining objects. */
void mm_end(MM *mm)
{
	int i;
	list_deallocate(mm->black);
	forn (i, MM_MAX_FREELIST) {
		if (mm->freelist[i] != NULL) {
			list_deallocate(mm->freelist[i]);
		}
	}
}

