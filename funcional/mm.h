#ifndef _MM_H_
#define _MM_H_

typedef char MMData;

#define	MM_KB	1024
#define	MM_MB	(1024 * MM_KB)

/* MM_FIRST_GC_THRESHOLD is the amount of allocated bytes that,
 * when reached, triggers GC for the very first time.
 */
#define MM_FIRST_GC_THRESHOLD	MM_MB
#define MAX(X, Y)		((X) < (Y) ? (Y) : (X))

/* The MMFlags type is used to represent both the size and the color
 * of an object.
 */

typedef unsigned long long int MMFlags;
typedef unsigned long long int MMSize;
typedef char MMColor;

#define MM_COLOR_NBITS				1
#define MM_MAX_FREELIST				1024
#define MM_FLAGS(SIZE, COLOR)			(((SIZE) << MM_COLOR_NBITS) | (COLOR))
#define MM_FLAGS_COLOR(FLAGS)			((FLAGS) & ((1 << MM_COLOR_NBITS) - 1))
#define MM_FLAGS_SIZE(FLAGS)			((FLAGS) >> MM_COLOR_NBITS)
#define MM_FLAGS_SET_COLOR(FLAGS, COLOR)	MM_FLAGS(MM_FLAGS_SIZE(FLAGS), (COLOR))

struct _MM;
struct _MMObject;

typedef void (*MMRefCallback)(struct _MM *, struct _MMObject *);
typedef void (*MMRefIterator)(struct _MM *, struct _MMObject *, MMRefCallback);

typedef struct _MMTag {
	MMRefIterator ref_iterator;
} MMTag;

typedef struct _MMObject {
	struct _MMObject *prev, *next;	/* Most objects belong to a doubly linked list. */
	MMFlags flags;			/* The flags for an object indicate its color and
				  	 * size. */
	MMTag *tag;			/* Tag indicating the type of the object.
					 * The main reason for the tag is
					 * being able to know which parts of an object data are
					 * pointers to other objects, for the memory
					 * manager to calculate reachability.
					 */
	MMData data[];			/* Raw data. */
} MMObject;

typedef struct _MM {
	/*
	 * Representation of the memory manager:
	 *
	 * - All MMObject instances are able to form doubly linked lists
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

	MMObject *black, *gray, *white;		/* Linked lists for the black, gray
						 * and white sets */
	MMObject *freelist[MM_MAX_FREELIST];	/* Linked list for the free cells */
	MMSize nalloc;				/* Amount of allocated memory in the black list */
	MMSize gc_threshold;			/* GC triggers when the allocated memory reaches
						 * this number of bytes */
	MMObject *root;				/* For marking the root */
	MMColor graycol;			/* Current gray color, (1 - graycol) is white
						 * color */
} MM;

void mm_gc(MM *mm);
void mm_init(MM *mm);
MMObject *mm_allocate(MM *mm, MMTag *tag, MMSize size);
void mm_end(MM *mm);

#endif
