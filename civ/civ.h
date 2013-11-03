#ifndef _CIV_H_
#define _CIV_H_

#include <stdlib.h>
#include "io.h"
#include "map.h"
#include "config.h"
#include "tribe.h"
#include "unit.h"

typedef struct _game_state {
	Config config;
	Map map;
	Unit ***unit_map;

	int ntribes;
	Tribe *tribe;
} GameState;

#endif
