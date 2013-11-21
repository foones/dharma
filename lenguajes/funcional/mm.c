#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "mm.h"

/*
 * Main idea of garbage collection:
 * - Newly allocated objects are colored black.
 * - For the mark phase:
 *       - set all nodes white
 *       - mark all reachable nodes black
 *       - gray nodes are known to be reachable but haven't been visited yet
 * - For the sweep phase:
 *       - erase all white nodes
 *
 * Invariant:
 * - Black nodes do not point to white nodes.
 */

/* Helpers */

#define whiten(X)	(X)->flags = Fu_MM_FLAGS_SET_COLOR((X)->flags, WHITE(mm))
#define grayen(X)	(X)->flags = Fu_MM_FLAGS_SET_COLOR((X)->flags, GRAY(mm))

#define forn(I, N)	for (I = 0; I < (N); i++)
#define foreach(X, L)	for (X = (L); X != NULL; X = X->next)

#define GRAY(mm)	(mm)->graycol
#define WHITE(mm)	(1 - GRAY(mm))

#define IS_WHITE(MM, X)	(Fu_MM_FLAGS_COLOR((X)->flags) == WHITE(MM))

static void list_remove(Fu_MMObject **list, Fu_MMObject *obj)
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

static Fu_MMObject *list_pop(Fu_MMObject **list)
{
	Fu_MMObject *obj = *list;
	list_remove(list, obj);
	return obj;
}

static void list_add_front(Fu_MMObject **list, Fu_MMObject *obj)
{
	obj->prev = NULL;
	obj->next = *list;
	if (*list != NULL) {
		(*list)->prev = obj;
	}
	*list = obj;
}

static void list_concat(Fu_MMObject **list1, Fu_MMObject **list2)
{
	while (*list2 != NULL) {
		list_add_front(list1, list_pop(list2));
	}
}

/* Invariant checker */

static void callback_check_not_white(Fu_MM *mm, Fu_Object *referenced)
{
	if (Fu_MM_IS_REFERENCE(referenced) && Fu_MM_FLAGS_COLOR(referenced->flags) == WHITE(mm)) {
		fprintf(stderr, "GC invariant broken; %p is white\n", referenced);
	}
}

static void gc_check_invariant(Fu_MM *mm)
{
	pthread_mutex_lock(&mm->allocate_mtx);
	Fu_MMObject *p;
	for (p = mm->black; p != NULL; p = p->next) {
		p->tag->ref_iterator(mm, p, callback_check_not_white);
	}
	pthread_mutex_unlock(&mm->allocate_mtx);
}

/* Fu_MM functions */

void fu_mm_init(Fu_MM *mm)
{
	int i;
	mm->black = NULL;
	mm->gray = NULL;
	mm->white = NULL;
	forn (i, Fu_MM_NUM_ROOTS) {
		mm->root[i] = NULL;
	}
	mm->nalloc = 0;
	mm->graycol = 0;
	mm->working = 1;
	forn (i, Fu_MM_MAX_FREELIST) {
		mm->freelist[i] = NULL;
	}

	pthread_mutex_init(&mm->allocate_mtx, NULL);
}

static void mark_as_gray(Fu_MM *mm, Fu_MMObject *referenced)
{
	if (Fu_MM_IS_REFERENCE(referenced) && Fu_MM_FLAGS_COLOR(referenced->flags) == WHITE(mm)) {
		list_remove(&mm->white, referenced);
		grayen(referenced);
		list_add_front(&mm->gray, referenced);
	}
}

void fu_mm_allocate(Fu_MM *mm, Fu_MMTag *tag, Fu_MMSize size, void *init, Fu_MMObject **out)
{
	pthread_mutex_lock(&mm->allocate_mtx);
	Fu_MMSize sz = sizeof(Fu_MMObject) + size;

	Fu_MMObject *obj;

	/* Get memory for the object */
	if (sz < Fu_MM_MAX_FREELIST && mm->freelist[sz] != NULL) {
		obj = list_pop(&mm->freelist[sz]);
	} else {
		obj = (Fu_MMObject *)malloc(sz);
	}

	obj->flags = Fu_MM_FLAGS(size, GRAY(mm));
	obj->tag = tag;
	obj->prev = NULL;
	list_add_front(&mm->black, obj);
	mm->nalloc += sz;

	assert(!Fu_MM_IS_IMMEDIATE(obj));

	/* Copy the initial data */
	memcpy(&obj->data, init, size);

	/*
	 * Ensure the garbage collector invariant is kept, i.e.
	 * grayen all the white nodes directly referenced from
	 * this one.
	 */
	tag->ref_iterator(mm, obj, mark_as_gray);
	*out = obj;

	pthread_mutex_unlock(&mm->allocate_mtx);
}

void fu_mm_set_gc_root(Fu_MM *mm, uint i, Fu_Object **root)
{
	pthread_mutex_lock(&mm->allocate_mtx);
	mm->root[i] = root;
	pthread_mutex_unlock(&mm->allocate_mtx);
}

#if 0
Fu_MMObject *fu_mm_store(Fu_MM *mm, Fu_Object *parent, Fu_Object **dst, Fu_Object *src)
{
	if (!Fu_MM_IS_REFERENCE(src)) {
		*dst = src;
		return;
	}

	assert(Fu_MM_IS_REFERENCE(parent));
	pthread_mutex_lock(...);
	if (Fu_MM_FLAGS_COLOR(parent->tag->flags) == GRAY(mm)
		&& Fu_MM_FLAGS_COLOR(src->tag->flags) == WHITE(mm)) {

	}
	pthread_mutex_unlock(...);
}
#endif

/* Mark all the objects white in O(1) */

static void whiten_all(Fu_MM *mm)
{
	mm->graycol = 1 - mm->graycol;
	assert(mm->white == NULL);
	mm->white = mm->black;
	list_concat(&mm->white, &mm->gray);
	mm->gray = NULL;
	mm->black = NULL;
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

static void list_deallocate(Fu_MMObject *list)
{
	Fu_MMObject *p;
	for (p = list; p != NULL;) {
		Fu_MMObject *obj = p;
		p = p->next;
		free(obj);
	}
}

/*
 * Free the big objects, and add the small objects to the
 * corresponding freelist.
 */
static void list_free(Fu_MM *mm, Fu_MMObject **list)
{
	Fu_MMObject *p;
	for (p = *list; p != NULL;) {
		Fu_MMObject *obj = p;
		Fu_MMSize sz = sizeof(Fu_MMObject) + Fu_MM_FLAGS_SIZE(obj->flags);
		p = p->next;

		assert(mm->nalloc >= sz);
		mm->nalloc -= sz;

		if (sz < Fu_MM_MAX_FREELIST) {
			list_add_front(&mm->freelist[sz], obj);
		} else {
			free(obj);
		}
	}
	*list = NULL;
}

/* Sweep */

static void sweep(Fu_MM *mm)
{
	list_free(mm, &mm->white);
	assert(mm->gray == NULL);
}

static void mark_sweep(Fu_MM *mm)
{
	pthread_mutex_lock(&mm->allocate_mtx);

	/* Whiten all objects */
	assert(mm->white == NULL);
	whiten_all(mm);

	/* Set the root gray */
	int i;
	forn (i, Fu_MM_NUM_ROOTS) {
		if (mm->root[i] == NULL || *mm->root[i] == NULL) continue;
		assert(Fu_MM_FLAGS_COLOR((*mm->root[i])->flags) == WHITE(mm));
		mark_as_gray(mm, *mm->root[i]);
	}

	pthread_mutex_unlock(&mm->allocate_mtx);

	/* While there are gray nodes */
	for (;;) {
		pthread_mutex_lock(&mm->allocate_mtx);

		if (mm->gray == NULL) {
			/* If no more gray nodes, sweep */
			sweep(mm);
			assert(mm->white == NULL);
			pthread_mutex_unlock(&mm->allocate_mtx);
			break;
		}

		/* Blacken the first gray object */
		Fu_MMObject *obj = list_pop(&mm->gray);
		assert(Fu_MM_FLAGS_COLOR(obj->flags) == GRAY(mm));

		list_add_front(&mm->black, obj);

		/* Grayen the white objects referenced by it */
		obj->tag->ref_iterator(mm, obj, mark_as_gray);

		pthread_mutex_unlock(&mm->allocate_mtx);
	}
}

/* Free all the remaining objects. */
void fu_mm_end(Fu_MM *mm)
{
	mm->working = 0;
}

/* Main concurrent garbage collector loop */
void *fu_mm_mainloop(void *mmptr)
{
	printf("empieza mainloop\n");

	/* Main loop */
	Fu_MM *mm = (Fu_MM *)mmptr;
	while (mm->working) {
		/*printf("gc\n");*/
		gc_check_invariant(mm);
		mark_sweep(mm);
		gc_check_invariant(mm);
	}

	/* Deallocate everything */
	int i;
	list_deallocate(mm->black);
	forn (i, Fu_MM_MAX_FREELIST) {
		if (mm->freelist[i] != NULL) {
			list_deallocate(mm->freelist[i]);
		}
	}
	pthread_mutex_destroy(&mm->allocate_mtx);

	return NULL;
}

