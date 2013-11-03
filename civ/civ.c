#include "civ.h"
#include "map.h"
#include "config.h"
#include "draw.h"

void game_add_unit(GameState *game_state, Tribe *tribe, Unit *unit, int i, int j)
{
	tribe_add_unit(tribe, unit);
}

void init_empty_game_state(GameState *game_state)
{
	init_config(&game_state->config);
	init_empty_map(&game_state->map);

	game_state->ntribes = 2;
	game_state->tribe = (Tribe *)malloc(sizeof(Tribe) * game_state->ntribes);
	init_tribe(&game_state->tribe[0], COL_TRIBE0, /*player=*/NULL);
	init_tribe(&game_state->tribe[1], COL_TRIBE1, /*player=*/NULL);

	game_add_unit(game_state, &game_state->tribe[0], unit_new(settlers), 0, 0);
	/*game_state->unit_map = NULL;*/
}

void refresh_screen(IO io, GameState *game_state)
{
	draw_game_state(io, game_state);
}

void advance_tribe(GameState *game_state, Tribe *t)
{
	//Unit *unit;
	/*
   for (unit = t->units; unit != NULL; unit = unit->next) {
		printf("mover unidad");
		//game_state->tribe[t]->player
	}
	*/
}

void advance_game(GameState *game_state)
{
	int t;
	for (t = 0; t < game_state->ntribes; t++) {
		advance_tribe(game_state, &game_state->tribe[t]);
	}
}

int main(int argc, char **argv) {
	IO io;
	GameState _game_state, *game_state = &_game_state;

	if (!io_init(&io)) {
		return 1;
	}

	init_empty_game_state(game_state);

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

