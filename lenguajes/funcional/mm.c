#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "Fu.h"

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

#define GRAY(mm)	(mm)->graycol
#define WHITE(mm)	(1 - GRAY(mm))

#define IS_WHITE(MM, X)	(Fu_MM_FLAGS_COLOR((X)->flags) == WHITE(MM))
#define IS_GRAY(MM, X)	(Fu_MM_FLAGS_COLOR((X)->flags) == GRAY(MM))

/* Invariant checker */

#if 0
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
	foreach (p, &mm->black) {
		p->tag->ref_iterator(mm, p, callback_check_not_white);
	}
	foreach (p, &mm->black) { assert(!IS_WHITE(mm, p)); }
	foreach (p, &mm->gray)  { assert(!IS_WHITE(mm, p)); }
	foreach (p, &mm->white) { assert(IS_WHITE(mm, p)); }
	pthread_mutex_unlock(&mm->allocate_mtx);
}
#endif

int gc_check_summary(Fu_MM *mm)
{
	Fu_Object *p;
	uint nobjs = 0;
	foreach (p, &mm->black) { assert(!IS_WHITE(mm, p)); nobjs++; }
	foreach (p, &mm->gray)  { assert(!IS_WHITE(mm, p)); nobjs++; }
	foreach (p, &mm->white) { assert(IS_WHITE(mm, p)); nobjs++; }
	printf("nobjs: %u\n", nobjs);
	printf("nalloc_objs: %llu\n", mm->nalloc_objs);
	return nobjs == mm->nalloc_objs;
}

/* Fu_MM functions */

void fu_mm_init(Fu_MM *mm)
{
	int i;
	fu_list_set_empty(&mm->black);
	fu_list_set_empty(&mm->gray);
	fu_list_set_empty(&mm->white);
	forn (i, Fu_MM_NUM_ROOTS) {
		mm->root[i] = NULL;
	}
	mm->nalloc = 0;
	mm->nalloc_objs = 0;
	mm->graycol = 0;
	mm->working = 1;
	forn (i, Fu_MM_MAX_FREELIST) {
		fu_list_set_empty(&mm->freelist[i]);
	}

	pthread_mutex_init(&mm->allocate_mtx, NULL);
}

static void mark_as_gray(Fu_MM *mm, Fu_MMObject *referenced)
{
	if (Fu_MM_IS_REFERENCE(referenced) && Fu_MM_FLAGS_COLOR(referenced->flags) == WHITE(mm)) {
		assert(!Fu_LIST_IS_EMPTY(&mm->white));
		fu_list_remove(&mm->white, referenced);
		grayen(referenced);
		fu_list_add_front(&mm->gray, referenced);
	}
	assert(gc_check_summary(mm));
}

Fu_Object *fu_mm_allocate_unmanaged(Fu_MMTag *tag, Fu_MMSize size)
{
	Fu_MMObject *obj = (Fu_MMObject *)malloc(sizeof(Fu_MMObject) + size);
	obj->flags = Fu_MM_FLAGS(size, 0);
	obj->tag = tag;
	obj->prev = NULL;
	obj->next = NULL;
	return obj;
}

void fu_mm_allocate(Fu_MM *mm, Fu_MMTag *tag, Fu_MMSize size, void *init, Fu_MMObject **out)
{
	pthread_mutex_lock(&mm->allocate_mtx);
	Fu_MMSize full_size = sizeof(Fu_MMObject) + size;

	Fu_MMObject *obj;

	/* Get memory for the object */
	if (full_size < Fu_MM_MAX_FREELIST && !Fu_LIST_IS_EMPTY(&mm->freelist[full_size])) {
		obj = fu_list_pop(&mm->freelist[full_size]);
	} else {
		obj = (Fu_MMObject *)malloc(full_size);
	}

	obj->flags = Fu_MM_FLAGS(size, GRAY(mm));
	obj->tag = tag;
	obj->prev = NULL;
	fu_list_add_front(&mm->black, obj);
	mm->nalloc += full_size;
	mm->nalloc_objs++;

	assert(!Fu_MM_IS_IMMEDIATE(obj));

	/* Copy the initial data */
	memcpy(obj->data, init, size);

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

void fu_mm_store(Fu_MM *mm, Fu_Object *parent, Fu_Object **location, Fu_Object *value)
{
	pthread_mutex_lock(&mm->allocate_mtx);
	if (!Fu_MM_IS_REFERENCE(value)) {
		*location = value;
	} else {
		assert(parent == NULL || Fu_MM_IS_REFERENCE(parent));
		if ((parent == NULL || IS_GRAY(mm, parent)) && IS_WHITE(mm, value)) {
			mark_as_gray(mm, value);
		}
		*location = value;
	}
	pthread_mutex_unlock(&mm->allocate_mtx);
}

/* Mark all the objects white in O(1) */

static void whiten_all(Fu_MM *mm)
{
	mm->graycol = 1 - mm->graycol;
	assert(Fu_LIST_IS_EMPTY(&mm->white));
	fu_list_set_copy(&mm->white, &mm->black);
	fu_list_concat(&mm->white, &mm->gray);
	fu_list_set_empty(&mm->gray);
	fu_list_set_empty(&mm->black);
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

static void list_deallocate(Fu_LinkedList *list)
{
	Fu_MMObject *p;
	for (p = list->first; p != NULL;) {
		Fu_MMObject *obj = p;
		p = p->next;
		free(obj);
	}
}

/*
 * Free the big objects, and add the small objects to the
 * corresponding freelist.
 */
static void list_free(Fu_MM *mm, Fu_LinkedList *list)
{
	Fu_MMObject *p;
	for (p = list->first; p != NULL;) {
		Fu_MMObject *obj = p;
		Fu_MMSize full_size = sizeof(Fu_MMObject) + Fu_MM_FLAGS_SIZE(obj->flags);
		p = p->next;

		assert(mm->nalloc >= full_size);
		mm->nalloc -= full_size;
		assert(mm->nalloc_objs >= 1);
		mm->nalloc_objs--;

		if (full_size < Fu_MM_MAX_FREELIST) {
			fu_list_add_front(&mm->freelist[full_size], obj);
		} else {
			free(obj);
		}
	}
	fu_list_set_empty(list);
}

/* Sweep */

static void sweep(Fu_MM *mm)
{
	list_free(mm, &mm->white);
	assert(Fu_LIST_IS_EMPTY(&mm->gray));
	mm->gc_threshold = 2 * mm->nalloc;
}

static void mark_sweep(Fu_MM *mm)
{
	pthread_mutex_lock(&mm->allocate_mtx);

	/* Whiten all objects */
	assert(Fu_LIST_IS_EMPTY(&mm->white));

	whiten_all(mm);

	/* Set the root gray */
	int i;
	forn (i, Fu_MM_NUM_ROOTS) {
		if (mm->root[i] == NULL || *mm->root[i] == NULL) continue;
		assert(Fu_MM_FLAGS_COLOR((*mm->root[i])->flags) == WHITE(mm));
		Fu_Object *obj = *mm->root[i];

		/* The root is *unmanaged*, hence we don't mark it gray.
		 * (Unmanaged nodes are never in the lists or freelists).
		 * We do mark all of its children gray. */
		printf("PASO\n");
		assert(obj->tag == &fu_vm_tag);
		obj->tag->ref_iterator(mm, obj, mark_as_gray);
		/*mark_as_gray(mm, obj);*/
	}

	assert(gc_check_summary(mm));

	pthread_mutex_unlock(&mm->allocate_mtx);

	/* While there are gray nodes */
	int break_outer = 0;
	for (;;) {
		pthread_mutex_lock(&mm->allocate_mtx);

		if (Fu_LIST_IS_EMPTY(&mm->gray)) {
			/* If no more gray nodes, sweep */
			sweep(mm);
			assert(Fu_LIST_IS_EMPTY(&mm->white));
			pthread_mutex_unlock(&mm->allocate_mtx);
			break_outer = 1;
			break;
		}

		/* Blacken the first gray object */
		Fu_MMObject *obj = fu_list_pop(&mm->gray);
		assert(Fu_MM_FLAGS_COLOR(obj->flags) == GRAY(mm));
		fu_list_add_front(&mm->black, obj);

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

#include <stdlib.h>
#include <unistd.h>
/* Main concurrent garbage collector loop */
void *fu_mm_mainloop(void *mmptr)
{
	/* Main loop */
	Fu_MM *mm = (Fu_MM *)mmptr;
	while (mm->working) {
		if (mm->nalloc > mm->gc_threshold) {
			printf("gc\n");
			mark_sweep(mm);
		}
	}

	/* Deallocate everything */
	int i;
	list_deallocate(&mm->black);
	forn (i, Fu_MM_MAX_FREELIST) {
		if (!Fu_LIST_IS_EMPTY(&mm->freelist[i])) {
			list_deallocate(&mm->freelist[i]);
		}
	}
	pthread_mutex_destroy(&mm->allocate_mtx);

	return NULL;
}

