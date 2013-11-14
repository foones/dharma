#include <stdlib.h>

#include "civ.h"
#include "map.h"
#include "view_config.h"
#include "draw.h"
#include "action.h"

int game_no_units_at(GameState *game_state, int i, int j)
{
	return game_state->unit_map[i][j].size == 0;
}

void game_position_unit_at(GameState *game_state, Unit *unit, int i, int j)
/* Doesn't erase the unit from the old position */
{
	assert(map_valid_pos(&game_state->map, i, j));
	assert(unit_can_step_on_terrain(unit, game_state->map.terrain[i][j]));
	unit->pos_i = i;
	unit->pos_j = j;
	UnitVector_add(&game_state->unit_map[i][j], unit);
}

int can_game_move_unit_to(GameState *game_state, Unit *unit, int i, int j)
/* Check that unit can step on the terrain */
{
	if (!unit_has_moves_left(unit)) {
		return 0;
	}
	if (i < 0 || i >= game_state->map.height || j < 0 || j >= game_state->map.width) {
		return 0;
	}
	if (!unit_can_step_on_terrain(unit, game_state->map.terrain[i][j])) {
		return 0;
	}
	return 1;
}

void game_move_unit_to(GameState *game_state, Unit *unit, int i, int j)
/* Also erases the unit from the old position */
{
	assert(can_game_move_unit_to(game_state, unit, i, j));
	UnitVector_remove1(&game_state->unit_map[unit->pos_i][unit->pos_j], unit);
	game_position_unit_at(game_state, unit, i, j);
	unit->moves_left--;
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
	init_empty_map(&game_state->map);

	game_state->ntribes = 2;

	/* Tribes */
	game_state->tribe = (Tribe *)malloc(sizeof(Tribe) * game_state->ntribes);
	init_tribe(&game_state->tribe[0], COL_TRIBE0);
	init_tribe(&game_state->tribe[1], COL_TRIBE1);

	/* Player for each tribe */
	game_state->tribe_player = (Player *)malloc(sizeof(Player) * game_state->ntribes);
	init_player(&game_state->tribe_player[0], PLAYER_INTERACTIVE, game_state, interactive_action_queue);
	init_player(&game_state->tribe_player[1], PLAYER_AI, game_state, NULL);

	INIT_MATRIX_BLOCK(game_state->unit_map,
				i, game_state->map.height,
				j, game_state->map.width, {
		UnitVector_init(&game_state->unit_map[i][j]);
	})

	game_add_unit(game_state, &game_state->tribe[0], settlers, 1, 0);
	game_add_unit(game_state, &game_state->tribe[0], settlers, 7, 1);
}

void refresh_screen(GameView *game_view)
{
	draw_game_view(game_view);
}

void local_set_current_unit(GameView *game_view, int u)
{
	GameState *game_state = game_view->game_state;
	Tribe *local_tribe = &game_state->tribe[game_state->current_tribe_index];
	game_view->current_unit = u;
	game_view->i_center = AT(local_tribe->units, u)->pos_i;
	game_view->j_center = AT(local_tribe->units, u)->pos_j;
}

void local_focus_on_next_unit(GameView *game_view)
{
	int n, i0, i;
	GameState *game_state = game_view->game_state;
	Tribe *local_tribe = &game_state->tribe[game_state->current_tribe_index];

	n = local_tribe->units->size;
	i0 = game_view->current_unit;
	if (i0 < 0 || i0 >= n) {
		i0 = n - 1;
	}

	game_view->end_of_turn = 1;
	for (i = (i0 + 1) % n; i != i0; i = (i + 1) % n) {
		if (unit_has_moves_left(AT(local_tribe->units, i))) {
			game_view->end_of_turn = 0;
			local_set_current_unit(game_view, i);
			break;
		}
	}
	printf("EOT: %u\n", game_view->end_of_turn);
}

void start_turn(GameView *game_view, Tribe *tribe)
{
	int i;
	for (i = 0; i < tribe->units->size; i++) {
		Unit *u = AT(tribe->units, i);
		u->hit_left = u->type->hit;
		u->moves_left = u->type->moves;
	}
	if (tribe->units->size < 1) {
		printf("la tribu no tiene mas unidades!!!!");
		exit(1);
	}
}

void local_start_turn(GameView *game_view)
{
	GameState *game_state = game_view->game_state;
	Tribe *local_tribe = &game_state->tribe[game_state->current_tribe_index];
	start_turn(game_view, local_tribe);
	local_focus_on_next_unit(game_view);
}

void turn_of_next_tribe(GameView *game_view)
{
	GameState *game_state = game_view->game_state;
	game_state->current_tribe_index = (game_state->current_tribe_index + 1) % game_state->ntribes;
	if (game_state->current_tribe_index == game_view->local_tribe_index) {
		local_start_turn(game_view);
	}
}

void advance_current_tribe(GameView *game_view)
{
	GameState *game_state = game_view->game_state;
	int tribe_index = game_state->current_tribe_index;
	/*Tribe *tribe = &game_state->tribe[tribe_index];*/
	Player *player = &game_state->tribe_player[tribe_index];
	if (player->type == PLAYER_AI) {
		/* TODO: code for AI mover */
		printf("playing with AI tribe %u\n", tribe_index);
		turn_of_next_tribe(game_view);
	}
}

/* Game view */
void init_game_view(GameView *game_view, GameState *game_state, IO io, ActionQueue *action_queue)
{
	game_view->game_state = game_state;
	game_view->io = io;
	game_view->action_queue = action_queue;

	init_view_config(&game_view->view_config);

	/* Start centering anywhere in the map */
	game_view->i_center = 0;
	game_view->j_center = 0;
}

int check_local_turn(GameView *game_view)
{
	return game_view->game_state->current_tribe_index == game_view->local_tribe_index;
}

int check_local_end_of_turn(GameView *game_view)
{
	return check_local_turn(game_view) && game_view->end_of_turn;
}

int check_turn_local_move_current_unit(GameView *game_view)
{
	GameState *game_state = game_view->game_state;
	if (!check_local_turn(game_view)) {
		return 0;
	}
	return 0 <= game_view->current_unit && game_view->current_unit < game_state->tribe->units->size;
}

Unit *current_local_unit_ptr(GameView *game_view)
{
	Tribe *local_tribe = &game_view->game_state->tribe[game_view->local_tribe_index];
	return AT(local_tribe->units, game_view->current_unit);
}

void viewport_for(GameView *game_view, Viewport *viewport)
{
	viewport->i0 = game_view->i_center - game_view->view_config.ncells_height / 2;
	viewport->i1 = viewport->i0 + game_view->view_config.ncells_height;
	viewport->j0 = game_view->j_center - game_view->view_config.ncells_width / 2;
	viewport->j1 = viewport->j0 + game_view->view_config.ncells_width;
}

int game_view_out_of_viewport_threshold(GameView *game_view, int i, int j, int threshold)
/* Returns true iff (i, j) is not in the viewport of the game view,
 * or if it is too close to the margin of the viewport
 */
{
	Viewport viewport;
	viewport_for(game_view, &viewport);
	return !(
		viewport.i0 + threshold <= i &&
		i <= viewport.i1 - threshold &&
		viewport.j0 + threshold <= j &&
		j <= viewport.j1 - threshold
	);
}

#define LOCAL_DISPLAY_WAIT_MILLISECS 400

void refresh_screen_and_wait_a_moment(GameView *game_view)
{
	refresh_screen(game_view);
	io_update(game_view->io);
	io_sleep(LOCAL_DISPLAY_WAIT_MILLISECS);
}

#define LOCAL_VIEWPORT_THRESHOLD 2	/* Distance to the border of the map that triggers
					 * centering the map on the place where the current
					 * focus is located.
					 */
void local_move_current_unit(GameView *game_view, int di, int dj)
{
	int i, j;
	Unit *u;
	if (!check_turn_local_move_current_unit(game_view)) {
		return;
	}
	u = current_local_unit_ptr(game_view);
	i = u->pos_i + di;
	j = u->pos_j + dj;


	if (can_game_move_unit_to(game_view->game_state, u, i, j)) {
		game_move_unit_to(game_view->game_state, u, i, j);
		if (game_view_out_of_viewport_threshold(game_view, i, j, LOCAL_VIEWPORT_THRESHOLD)) {
			game_view->i_center = i;
			game_view->j_center = j;
		}
	}
	if (!unit_has_moves_left(u)) {
		game_view->blink = 0;
		refresh_screen_and_wait_a_moment(game_view);
		local_focus_on_next_unit(game_view);
	}
}

void update_game_view_on_key(GameView *game_view, int key)
{
	switch (key) {
	case 'H': game_view->j_center--; break;
	case 'J': game_view->i_center++; break;
	case 'K': game_view->i_center--; break;
	case 'L': game_view->j_center++; break;

	case 'h': local_move_current_unit(game_view, 0, -1); break;
	case 'l': local_move_current_unit(game_view, 0, 1); break;
	case 'j': local_move_current_unit(game_view, 1, 0); break;
	case 'k': local_move_current_unit(game_view, -1, 0); break;

	case 'n': local_focus_on_next_unit(game_view); break;
	case '\r':
		{
			if (check_local_end_of_turn(game_view)) {
				turn_of_next_tribe(game_view);
			}
			break;
		}
	}
}

int main(int argc, char **argv) {
	IO io;

	GameState _game_state, *game_state = &_game_state;
	GameView _game_view, *game_view = &_game_view;
	ActionQueue _interactive_action_queue, *interactive_action_queue = &_interactive_action_queue;

	if (!io_init(&io)) {
		return 1;
	}

	init_empty_game_state(game_state, interactive_action_queue);
	init_game_view(game_view, game_state, io, interactive_action_queue);

	game_view->blink = 0;		/* start blinking */
	game_view->local_tribe_index = 0; /* index of the tribe that is controlled by the player */

	game_state->current_tribe_index = 0; /* index of the tribe that is currently moving */

	local_start_turn(game_view);

	while (1) {
		/* Refresh screen */
		io_update(io);
		game_view->blink = (game_view->blink + 1) % 20;
		refresh_screen(game_view);

		advance_current_tribe(game_view);

		/* Get input */
		int key = io_get_key();
		if (key == 27) {
			break;
		}
		if (key != -1) {
			update_game_view_on_key(game_view, key);
			printf("%u\n", key % 256);
		}

		/** TODO **/

	}

	return 0;
}

