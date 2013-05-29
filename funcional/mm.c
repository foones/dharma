#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "mm.h"

/* Helpers */

#define whiten(X)	(X)->flags = MM_FLAGS_SET_COLOR((X)->flags, WHITE(mm))
#define grayen(X)	(X)->flags = MM_FLAGS_SET_COLOR((X)->flags, GRAY(mm))

#define foreach(X, L)	for (X = (L); X != NULL; X = X->next)

#define GRAY(mm)	(mm)->graycol
#define WHITE(mm)	(1 - GRAY(mm))

void list_remove(MMObject **list, MMObject *obj)
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

void list_add_front(MMObject **list, MMObject *obj)
{
	obj->next = *list;
	if (*list != NULL) {
		(*list)->prev = obj;
	}
	*list = obj;
}

/* MM functions */

void mm_init(MM *mm)
{
	mm->objects = NULL;
	mm->root = NULL;
	mm->nalloc = 0;
	mm->gray = NULL;
	mm->black = NULL;
	mm->graycol = 0;
	mm->gc_threshold = MM_MIN_GC_THRESHOLD;
}

MMObject *mm_allocate(MM *mm, MMTag *tag, MMSize size)
{
	MMSize nalloc = sizeof(MMObject) + size;

	if (mm->nalloc + nalloc > mm->gc_threshold) {
		mm_gc(mm);
	}

	MMObject *obj = (MMObject *)malloc(nalloc);
	obj->tag = tag;
	obj->flags = MM_FLAGS(size, GRAY(mm));
	obj->prev = NULL;
	list_add_front(&mm->objects, obj);
	mm->nalloc += nalloc;
	return obj;
}

/* Mark clearing */

static void whiten_all(MM *mm)
{
	mm->graycol = 1 - mm->graycol;
}

/* Mark */

static void mark_as_gray(MM *mm, MMObject *referenced)
{
	if (referenced != NULL && MM_FLAGS_COLOR(referenced->flags) == WHITE(mm)) {
		list_remove(&mm->objects, referenced);
		grayen(referenced);
		list_add_front(&mm->gray, referenced);
	}
}

static void mark(MM *mm)
{
	assert(mm->root != NULL);
	assert(mm->black == NULL);
	assert(mm->gray == NULL);

	/* Whiten all objects */
	whiten_all(mm);

	/* Set the root gray */
	assert(MM_FLAGS_COLOR(mm->root->flags) == WHITE(mm));
	mark_as_gray(mm, mm->root);

	/* While there are gray nodes */
	while (mm->gray != NULL) {
		/* Blacken the first gray object */
		MMObject *obj = mm->gray;
		assert(MM_FLAGS_COLOR(obj->flags) == GRAY(mm));
		list_remove(&mm->gray, obj);
		list_add_front(&mm->black, obj);

		/* Grayen the white objects referenced by it */
		obj->tag->ref_iterator(mm, obj, mark_as_gray);
	}
}

/* Sweep */

static void sweep(MM *mm)
{
	MMObject *p;
	for (p = mm->objects; p != NULL;) {
		assert(MM_FLAGS_COLOR(p->flags) == WHITE(mm));
		MMObject *obj = p;
		MMSize sz = MM_FLAGS_SIZE(obj->flags);
		p = p->next;
		assert(mm->nalloc >= sizeof(MMObject) + sz);
		mm->nalloc -= sizeof(MMObject) + sz;
		free(obj);
	}
	mm->gc_threshold = MAX(2 * mm->nalloc, MM_MIN_GC_THRESHOLD);
	assert(mm->black != NULL);
	mm->objects = mm->black;
	mm->black = NULL;
	assert(mm->gray == NULL);
}

/* Garbage collection */

void mm_gc(MM *mm)
{
	printf("gc\n");
	mark(mm);
	sweep(mm);
}

