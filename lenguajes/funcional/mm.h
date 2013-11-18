#ifndef _FU_MM_H_
#define _FU_MM_H_

#include "common.h"

typedef uchar Fu_MMData;

#define Fu_MM_NBITS_PADDING		3
#define Fu_MM_IMMEDIATE_MASK		((((uint64)1) << Fu_MM_NBITS_PADDING) - 1)
#define Fu_MM_MK_IMMEDIATE(X, TAG)	((Fu_Object *)((X) << Fu_MM_NBITS_PADDING | (TAG)))
#define Fu_MM_IMMEDIATE_TAG(X)		((uint64)(X) & Fu_MM_IMMEDIATE_MASK)
#define Fu_MM_IS_IMMEDIATE(X)		(Fu_MM_IMMEDIATE_TAG(X) != 0x0)
#define Fu_MM_IMMEDIATE_VALUE(X)	((uint64)(X) >> Fu_MM_NBITS_PADDING)

/* For an object to be a reference it has to be both:
 * - non-null
 * - not inmediate
 */
#define Fu_MM_IS_REFERENCE(X)		((X) != NULL && !Fu_MM_IS_IMMEDIATE(X))

/* Fu_MM_FIRST_GC_THRESHOLD is the amount of allocated bytes that,
 * when reached, triggers GC for the very first time.
 */
#define Fu_MM_FIRST_GC_THRESHOLD	Fu_MB
#define MAX(X, Y)			((X) < (Y) ? (Y) : (X))

/* The Fu_MMFlags type is used to represent both the size and the color
 * of an object.
 */

typedef unsigned long long int Fu_MMFlags;
typedef unsigned long long int Fu_MMSize;
typedef char Fu_MMColor;

#define Fu_MM_COLOR_NBITS				1
#define Fu_MM_MAX_FREELIST				1024
#define Fu_MM_FLAGS(SIZE, COLOR)			(((SIZE) << Fu_MM_COLOR_NBITS) | (COLOR))
#define Fu_MM_FLAGS_COLOR(FLAGS)			((FLAGS) & ((1 << Fu_MM_COLOR_NBITS) - 1))
#define Fu_MM_FLAGS_SIZE(FLAGS)			((FLAGS) >> Fu_MM_COLOR_NBITS)
#define Fu_MM_FLAGS_SET_COLOR(FLAGS, COLOR)	Fu_MM_FLAGS(Fu_MM_FLAGS_SIZE(FLAGS), (COLOR))

/* Object */

struct _Fu_MM;
struct _Fu_MMObject;

typedef void (*Fu_MMRefCallback)(struct _Fu_MM *, struct _Fu_MMObject *);
typedef void (*Fu_MMRefIterator)(struct _Fu_MM *, struct _Fu_MMObject *, Fu_MMRefCallback);

typedef struct _Fu_MMTag {
	Fu_MMRefIterator ref_iterator;
} Fu_MMTag;

typedef struct _Fu_MMObject {
	struct _Fu_MMObject *prev, *next;	/* Most objects belong to a doubly linked list. */
	Fu_MMFlags flags;			/* The flags for an object indicate its color and
						 * size. */
	Fu_MMTag *tag;			/* Tag indicating the type of the object.
					 * The main reason for the tag is
					 * being able to know which parts of an object data are
					 * pointers to other objects, for the memory
					 * manager to calculate reachability.
					 */
	Fu_MMData data[];		/* Raw data. */
} Fu_MMObject;

/* Memory manager */

typedef struct _Fu_MM {
	/*
	 * Representation of the memory manager:
	 *
	 * - All Fu_MMObject instances are able to form doubly linked lists
	 *   by means of their prev and next fields.
	 *
	 * - <graycol> indicates which is the current gray color.
	 *   1 - graycol is the current white color. There is no explicit
	 *   black color.
	 *
	 * - <objects> is the doubly linked list of all the live objects
	 *   in the system. All the objects in this list are
	 *   normally colored gray, except during GC.
	 *
	 * - <root> is expected to be the root object, which should
	 *   reach all the relevant objects in the system.
	 *
	 * - <black> and <gray> are auxiliary linked lists that should
	 *   be normally empty (NULL), and should only be used during
	 *   GC.
	 *
	 */

	Fu_MMObject *black, *gray, *white;		/* Linked lists for the black, gray
						 * and white sets */
	Fu_MMObject *freelist[Fu_MM_MAX_FREELIST];	/* Linked list for the free cells,
						 * indexed by the allocation size */
	Fu_MMSize nalloc;				/* Amount of allocated memory in the black list */
	Fu_MMSize gc_threshold;			/* GC triggers when the allocated memory reaches
						 * this number of bytes */
	Fu_MMObject *root;				/* For marking the root */
	Fu_MMColor graycol;			/* Current gray color, (1 - graycol) is white
						 * color */
} Fu_MM;

void fu_mm_gc(Fu_MM *mm);
void fu_mm_init(Fu_MM *mm);
Fu_MMObject *fu_mm_allocate(Fu_MM *mm, Fu_MMTag *tag, Fu_MMSize size);
void fu_mm_end(Fu_MM *mm);

#endif
