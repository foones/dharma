#include "civ.h"

void init_player(Player *player, PlayerType player_type, GameState *game_state, ActionQueue *action_queue)
{
	player->type = player_type;
	player->game_state = game_state;
	player->action_queue = action_queue;
}

