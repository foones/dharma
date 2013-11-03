#ifndef _CIVTRIBE_H_
#define _CIVTRIBE_H_

#include "io.h"
#include "player.h"
#include "unit.h"
#include "utils.h"
#include "config.h"

typedef struct _tribe {
	Color color;
	Player *player;
	UnitVector *units;
} Tribe;

void init_tribe(Tribe *tribe, Color color, Player *player);
void tribe_add_unit(Tribe *tribe, Unit *unit);

#endif
