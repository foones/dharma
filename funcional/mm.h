#ifndef _MM_H_
#define _MM_H_

typedef char MMData;
typedef unsigned long long int MMFlags;
typedef unsigned long long int MMSize;
typedef char MMColor;

#define MM_BLACK				0x0
#define MM_WHITE				0x1
#define MM_FLAGS(SIZE, COLOR)			(((SIZE) << 1) | (COLOR))
#define MM_FLAGS_SET_COLOR(FLAGS, COLOR)	((((FLAGS) >> 1) << 1) | (COLOR))
#define MM_FLAGS_COLOR(FLAGS)			((FLAGS) & 0x1)
#define MM_FLAGS_SIZE(FLAGS)			((FLAGS) >> 1)

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
	/*struct _MMObject *prev, *next;*/
	struct _MMObject *next;
	MMFlags flags;
	MMData data[];
} MMObject;

typedef struct _MMTag {
	MMRefIterator ref_iterator;
} MMTag;

typedef struct _MM {
	MMObject *objects;
	MMObject *root;
	MMSize nalloc;
	MMSize gc_threshold;
} MM;

void mm_gc(MM *mm);
void mm_init(MM *mm);
MMObject *mm_allocate(MM *mm, MMTag *tag, MMSize size);

#endif
