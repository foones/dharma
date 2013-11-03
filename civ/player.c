#include "civ.h"

void init_player(Player *player, GameState *game_state, ActionQueue *action_queue)
{
	player->type = PLAYER_INTERACTIVE;
	player->game_state = game_state;
	player->action_queue = action_queue;
}

int player_movement_for(Player *player, Unit *unit)
{
	// revisar action queue y desencolar :)
	return 22;
}

