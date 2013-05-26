#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

typedef char MMData;
typedef long long int MMSize;
typedef int MMColor;

#define	KB	1024
#define	MB	(1024 * KB)

#define MIN_GC_SIZE	MB
#define MAX(X, Y)	((X) < (Y) ? (Y) : (X))

#define MM_BLACK	0
#define MM_WHITE	1

struct _MM;
struct _MMObject;

typedef void (*MMRefCallback)(struct _MM *, struct _MMObject *);
typedef void (*MMRefIterator)(struct _MM *, struct _MMObject *, MMRefCallback);

typedef struct _MMObject {
	struct _MMTag *tag;
	struct _MMObject *next;
	MMSize size;
	MMColor color;
	MMData data[];
} MMObject;

typedef struct _MMTag {
	MMRefIterator ref_iterator;
} MMTag;

typedef struct _MM {
	MMObject *objects;
	MMObject *root;
	MMSize nalloc;
	MMSize next_gc;
} MM;

void mm_gc(MM *mm);

void mm_init(MM *mm)
{
	mm->objects = NULL;
	mm->root = NULL;
	mm->nalloc = 0;
	mm->next_gc = MIN_GC_SIZE;
}

MMObject *mm_allocate(MM *mm, MMTag *tag, int size)
{
	MMSize nalloc = sizeof(MMObject) + size * sizeof(MMData);

	if (mm->nalloc + nalloc > mm->next_gc) {
		mm_gc(mm);
	}

	MMObject *obj = (MMObject *)malloc(nalloc);
	obj->tag = tag;
	obj->size = size * sizeof(MMData);
	obj->color = MM_BLACK;
	obj->next = mm->objects;
	mm->objects = obj;
	mm->nalloc += nalloc;
	return obj;
}

/* Mark clearing */

void mm_mark_all(MM *mm, MMColor col)
{
	MMObject *p;
	for (p = mm->objects; p != NULL; p = p->next) {
		p->color = col;
	}
}

/* Mark */

void mm_mark_reachable(MM *mm, MMObject *root);

static void mark_as_reachable(MM *mm, MMObject *referenced)
{
	if (referenced != NULL && referenced->color == MM_WHITE) {
		mm_mark_reachable(mm, referenced);
	}
}

void mm_mark_reachable(MM *mm, MMObject *root)
{
	assert(root != NULL);
	if (root->color != MM_BLACK) {
		root->color = MM_BLACK;
		root->tag->ref_iterator(mm, root, mark_as_reachable);
	}
}

void mm_mark(MM *mm)
{
	assert(mm->root != NULL);
	mm_mark_all(mm, MM_WHITE);
	mm_mark_reachable(mm, mm->root);
}

/* Sweep */

void mm_sweep(MM *mm)
{
	MMObject **p;
	for (p = &mm->objects; *p != NULL;) {
		if ((*p)->color == MM_WHITE) {
			MMObject *obj = *p;
			*p = (*p)->next;
			assert(mm->nalloc >= sizeof(MMObject) + obj->size);
			mm->nalloc -= sizeof(MMObject) + obj->size;
			free(obj);
		} else {
			p = &(*p)->next;
		}
	}
	mm->next_gc = MAX(2 * mm->nalloc, MIN_GC_SIZE);
}

/* Garbage collection */

void mm_gc(MM *mm)
{
	printf("gc\n");
	mm_mark(mm);
	mm_sweep(mm);
}

/* Main */

void cons_ref_iterator(MM *mm, MMObject *cons_cell, MMRefCallback callback)
{
	MMObject *car = ((MMObject **)cons_cell->data)[0];
	MMObject *cdr = ((MMObject **)cons_cell->data)[1];
	callback(mm, car);
	callback(mm, cdr);
}

MMTag cons_cell_tag = { cons_ref_iterator };

MMObject *mk_cons_cell(MM *mm, MMObject *car, MMObject *cdr)
{
	MMObject *cons_cell = mm_allocate(mm, &cons_cell_tag, 2 * sizeof(MMObject *));
	((MMObject **)cons_cell->data)[0] = car;
	((MMObject **)cons_cell->data)[1] = cdr;
	return cons_cell;
}

int main()
{
	MM _mm;
	MM *mm = &_mm;

	mm_init(mm);
	mm->root = mk_cons_cell(mm, NULL, NULL);

	MMObject *lst;
	for (int i = 0; i < 100000; i++) {
		if (i % 3 == 0) {
			lst = mk_cons_cell(mm, lst, lst);
			mm->root = lst;
		} else {
			mk_cons_cell(mm, lst, lst);
		}
		printf("nalloc: %llu next_gc: %llu\n", mm->nalloc, mm->next_gc);
	}

	return 0;
}

