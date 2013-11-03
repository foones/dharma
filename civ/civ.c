#include "civ.h"
#include "map.h"
#include "config.h"
#include "draw.h"
#include "action.h"

int game_no_units_at(GameState *game_state, int i, int j)
{
	return game_state->unit_map[i][j] == NULL;
}

void game_position_unit_at(GameState *game_state, Unit *unit, int i, int j)
{
	assert(map_valid_pos(&game_state->map, i, j));
	assert(unit_can_step_on_terrain(unit, game_state->map.terrain[i][j]));
	assert(game_no_units_at(game_state, i, j));
	unit->pos_i = i;
	unit->pos_j = j;
	game_state->unit_map[i][j] = unit;
}

void game_add_unit(GameState *game_state, Tribe *tribe, UnitType *unit_type, int i, int j)
{
	Unit *unit = unit_new(unit_type);
	unit->tribe = tribe;
	tribe_add_unit(tribe, unit);
	game_position_unit_at(game_state, unit, i, j);
}

void init_empty_game_state(GameState *game_state, ActionQueue *interactive_action_queue)
{
	init_config(&game_state->config);
	init_empty_map(&game_state->map);

	game_state->ntribes = 2;

	/* Tribes */
	game_state->tribe = (Tribe *)malloc(sizeof(Tribe) * game_state->ntribes);
	init_tribe(&game_state->tribe[0], COL_TRIBE0);
	init_tribe(&game_state->tribe[1], COL_TRIBE1);

	/* Player for each tribe */
	game_state->tribe_player = (Player *)malloc(sizeof(Player) * game_state->ntribes);
	init_player(&game_state->tribe_player[0], game_state, interactive_action_queue);
	init_player(&game_state->tribe_player[1], game_state, NULL);

	INIT_MATRIX(game_state->unit_map, game_state->map.height, game_state->map.width, NULL);

	game_add_unit(game_state, &game_state->tribe[0], settlers, 1, 0);
}

void refresh_screen(IO io, GameState *game_state)
{
	draw_game_state(io, game_state);
}

void advance_tribe(GameState *game_state, int tribe_index, Tribe *tribe)
{
	int i;
	for (i = 0; i < tribe->units->size; i++) {
		Unit *unit = AT(tribe->units, i);
		Player *player = &game_state->tribe_player[tribe_index];
		int movement = player_movement_for(player, unit);
		printf("mover unidad %p %p %u\n", unit, player, movement);
	}
}

void advance_game(GameState *game_state)
{
	int t;
	for (t = 0; t < game_state->ntribes; t++) {
		advance_tribe(game_state, t, &game_state->tribe[t]);
	}
}

int main(int argc, char **argv) {
	IO io;
	GameState _game_state, *game_state = &_game_state;
	ActionQueue _interactive_action_queue;
	ActionQueue *interactive_action_queue = &_interactive_action_queue;

	if (!io_init(&io)) {
		return 1;
	}

	init_empty_game_state(game_state, interactive_action_queue);

	while (1) {
		/* Refresh screen */
		io_update(io);
		refresh_screen(io, game_state);
		advance_game(game_state);

		/* Get input */
		int key = io_get_key();
		if (key == 27) {
			break;
		}
		if (key != -1) {
			printf("%u\n", key % 256);
		}
	}

	return 0;
}

