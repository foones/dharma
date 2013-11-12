#ifndef _PLAYER_H_
#define _PLAYER_H_

#include "action.h"
#include "civ.h"

typedef int PlayerType;

#define PLAYER_INTERACTIVE	1
#define PLAYER_AI		2

typedef struct _player {
	PlayerType type;

	GameState *game_state;
	ActionQueue *action_queue;
} Player;

void init_player(Player *player, PlayerType player_type, GameState *game_state, ActionQueue *action_queue);

#endif
