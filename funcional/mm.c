#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "mm.h"

void mm_init(MM *mm)
{
	mm->objects = NULL;
	mm->root = NULL;
	mm->nalloc = 0;
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
	obj->flags = MM_FLAGS(size, MM_BLACK);
	obj->next = mm->objects;
	mm->objects = obj;
	mm->nalloc += nalloc;
	return obj;
}

/* Mark clearing */

static void mark_all(MM *mm, MMColor color)
{
	MMObject *p;
	for (p = mm->objects; p != NULL; p = p->next) {
		p->flags = MM_FLAGS_SET_COLOR(p->flags, color);
	}
}

/* Mark */

static void mark_reachable(MM *mm, MMObject *root);

static void mark_as_reachable(MM *mm, MMObject *referenced)
{
	if (referenced != NULL && MM_FLAGS_COLOR(referenced->flags) == MM_WHITE) {
		mark_reachable(mm, referenced);
	}
}

static void mark_reachable(MM *mm, MMObject *root)
{
	assert(root != NULL);
	if (MM_FLAGS_COLOR(root->flags) != MM_BLACK) {
		root->flags = MM_FLAGS_SET_COLOR(root->flags, MM_BLACK);
		root->tag->ref_iterator(mm, root, mark_as_reachable);
	}
}

static void mark(MM *mm)
{
	assert(mm->root != NULL);
	mark_all(mm, MM_WHITE);
	mark_reachable(mm, mm->root);
}

/* Sweep */

static void sweep(MM *mm)
{
	MMObject **p;
	for (p = &mm->objects; *p != NULL;) {
		if (MM_FLAGS_COLOR((*p)->flags) == MM_WHITE) {
			MMObject *obj = *p;
			MMSize sz = MM_FLAGS_SIZE(obj->flags);
			*p = (*p)->next;
			assert(mm->nalloc >= sizeof(MMObject) + sz);
			mm->nalloc -= sizeof(MMObject) + sz;
			free(obj);
		} else {
			p = &(*p)->next;
		}
	}
	mm->gc_threshold = MAX(2 * mm->nalloc, MM_MIN_GC_THRESHOLD);
}

/* Garbage collection */

void mm_gc(MM *mm)
{
	printf("gc\n");
	mark(mm);
	sweep(mm);
}

