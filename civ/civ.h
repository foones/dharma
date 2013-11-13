#ifndef _CIV_H_
#define _CIV_H_

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef struct _game_state GameState;

#include "io.h"
#include "map.h"
#include "view_config.h"
#include "tribe.h"
#include "unit.h"
#include "player.h"

struct _game_state {
	Map map;
	Unit ***unit_map;

	int ntribes;
	Tribe *tribe;
	Player *tribe_player;

	int current_tribe_index;
};

typedef struct _game_view {
	ViewConfig view_config;
	GameState *game_state;
	IO io;
	int i_center, j_center;		/* current i and j values that we are centering on */
	ActionQueue *action_queue;
	int current_unit;		/* current unit on focus */
	int local_tribe_index;		/* index of the local tribe in the game state */
	unsigned int blink;		/* blink counter for the current unit on focus */
	int end_of_turn;		/* is it the end of my turn? */
} GameView;

#endif
