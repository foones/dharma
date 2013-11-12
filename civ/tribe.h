#ifndef _CIVTRIBE_H_
#define _CIVTRIBE_H_

#include "io.h"
#include "unit.h"
#include "utils.h"
#include "view_config.h"

typedef struct _tribe {
	Color color;
	UnitVector *units;
} Tribe;

void init_tribe(Tribe *tribe, Color color);
void tribe_add_unit(Tribe *tribe, Unit *unit);

#endif
