#ifndef _CIV_H_
#define _CIV_H_

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef struct _game_state GameState;

#include "io.h"
#include "map.h"
#include "config.h"
#include "tribe.h"
#include "unit.h"
#include "player.h"

struct _game_state {
	Config config;
	Map map;
	Unit ***unit_map;

	int ntribes;
	Tribe *tribe;
	Player *tribe_player;
};

#endif
