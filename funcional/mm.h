#ifndef _MM_H_
#define _MM_H_

typedef char MMData;
typedef unsigned long long int MMFlags;
typedef unsigned long long int MMSize;
typedef char MMColor;

#define MM_COLOR_NBITS				1
#define MM_FLAGS(SIZE, COLOR)			(((SIZE) << MM_COLOR_NBITS) | (COLOR))
#define MM_FLAGS_COLOR(FLAGS)			((FLAGS) & ((1 << MM_COLOR_NBITS) - 1))
#define MM_FLAGS_SIZE(FLAGS)			((FLAGS) >> MM_COLOR_NBITS)
#define MM_FLAGS_SET_COLOR(FLAGS, COLOR)	MM_FLAGS(MM_FLAGS_SIZE(FLAGS), (COLOR))

#define	MM_KB	1024
#define	MM_MB	(1024 * MM_KB)

#define MM_MIN_GC_THRESHOLD	MM_MB
#define MAX(X, Y)		((X) < (Y) ? (Y) : (X))

struct _MM;
struct _MMObject;

typedef void (*MMRefCallback)(struct _MM *, struct _MMObject *);
typedef void (*MMRefIterator)(struct _MM *, struct _MMObject *, MMRefCallback);

typedef struct _MMObject {
	struct _MMTag *tag;
	struct _MMObject *prev, *next; MMFlags flags;
	MMData data[];
} MMObject;

typedef struct _MMTag {
	MMRefIterator ref_iterator;
} MMTag;

typedef struct _MM {
	MMObject *objects;	/* Pointer to one of the live objects
				   	in the system, which form a doubly
					linked list */
	MMSize nalloc;		/* Amount of allocated memory in bytes */
	MMSize gc_threshold;	/* GC triggers when the allocated memory reaches
				 	this number of bytes */
	MMObject *root;		/* For marking the root */
	MMObject *black, *gray;	/* For the temporary black and gray sets */

	MMColor graycol;	/* Current gray color, (1 - graycol) is white color */
} MM;

void mm_gc(MM *mm);
void mm_init(MM *mm);
MMObject *mm_allocate(MM *mm, MMTag *tag, MMSize size);

#endif
