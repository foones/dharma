#ifndef _CIVACTION_H_
#define _CIVACTION_H_

#include "utils.h"

typedef struct _action {
	int XXX;
} Action;

#define ACTION_QUEUE_CAPACITY	16384

DECLARE_QUEUE_TYPE(ActionQueue, Action *)

#endif
