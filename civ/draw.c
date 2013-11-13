#include <assert.h>
#include "tribe.h"
#include "draw.h"

static void draw_rectangle(IO io, ViewConfig *view_config, int x0, int y0, int width, int height, Color outline, Color fill)
{
	int x, y;
	int x1 = x0 + width;
	int y1 = y0 + height;
	for (x = x0; x < x1; x++) {
		for (y = y0; y < y1; y++) {
			IOColor iocolor;
			if (x == x0 || x == x1 - 1 || y == y0 || y == y1 - 1) {
				iocolor = view_config->palette[outline];
			} else {
				iocolor = view_config->palette[fill];
			}
			io_draw_point(io, x, y, iocolor);
		}
	}
}

/* Version with decorations */
static void draw_terrain_rectangle(IO io, ViewConfig *view_config, int x0, int y0, int width, int height, Color outline, Color fill)
{
	int x, y;
	int x1 = x0 + width;
	int y1 = y0 + height;
	for (x = x0; x < x1; x++) {
		for (y = y0; y < y1; y++) {
			int tmi, tmj;
			unsigned char modifier;
			IOColor iocolor;
			if (x == x0 || y == y0) {
				iocolor = view_config->palette[outline];
			} else {
				iocolor = view_config->palette[fill];
			}
			tmi = ((int)(TERRAIN_MODEL_SIZE * (double)(x - x0) / (double)width));
			tmj = ((int)(TERRAIN_MODEL_SIZE * (double)(y - y0) / (double)height));
			assert(tmi < TERRAIN_MODEL_SIZE);
			assert(tmj < TERRAIN_MODEL_SIZE);
			modifier = view_config->terrain_model[tmi][tmj];
			if (modifier < 128) modifier = 196;
			iocolor = io_color(
					(int)((double)io_color_red(iocolor) * ((double)modifier / (double)255)),
					(int)((double)io_color_green(iocolor) * ((double)modifier / (double)255)),
					(int)((double)io_color_blue(iocolor) * ((double)modifier / (double)255))
			);
			io_draw_point(io, x, y, iocolor);
			
		}
	}
}

static void draw_circle(IO io, ViewConfig *view_config, int x0, int y0, int width, int height, Color fill)
{
	draw_rectangle(io, view_config, x0 + 10, y0 + 10, width - 20, height - 20, fill, fill);
}

static void draw_terrain(IO io, ViewConfig *view_config, int x, int y, Terrain *terrain)
{
	//draw_rectangle(io, view_config, x, y, view_config->cell_size, view_config->cell_size, empty_cell_color, terrain->color);
	draw_terrain_rectangle(io, view_config, x, y, view_config->cell_size, view_config->cell_size, empty_cell_color, terrain->color);
}

static void draw_unit(IO io, ViewConfig *view_config, int x, int y, Unit *unit)
{
	draw_circle(io, view_config, x, y, view_config->cell_size, view_config->cell_size, unit->tribe->color);
}

static void draw_empty_cell(IO io, ViewConfig *view_config, int x, int y)
{
	draw_rectangle(io, view_config, x, y, view_config->cell_size, view_config->cell_size, empty_cell_color, empty_cell_color);
}

extern Unit *current_local_unit_ptr(GameView *game_view);
extern void viewport_for(GameView *game_view, Viewport *viewport);

static int blink_for_unit(GameView *game_view, Unit *unit)
{
	if (game_view->end_of_turn) {
		return 0;
	}
	if (unit == current_local_unit_ptr(game_view)) {
		return game_view->blink;
	}
	return 0;
}

static int blink_is_on(int blink)
{
	return blink % 16 < 8;
}

static void draw_map(GameView *game_view, ViewConfig *view_config, IO io, GameState *game_state, int i_center, int j_center)
{
	Map *map = &game_state->map; 
	Unit ***unit_map = game_state->unit_map; 

	int i, j;
	int x, y;
	int i0, i1, j0, j1;
	Viewport viewport;

	viewport_for(game_view, &viewport);
	i0 = viewport.i0;
	i1 = viewport.i1;
	j0 = viewport.j0;
	j1 = viewport.j1;

	for (i = i0, y = view_config->map_y0; i < i1; i++, y += view_config->cell_size) {
		for (j = j0, x = view_config->map_x0; j < j1; j++, x+= view_config->cell_size) {
			if (map_valid_pos(map, i, j)) {
				draw_terrain(io, view_config, x, y, map->terrain[i][j]);
				if (unit_map[i][j] != NULL) {
					if (blink_is_on(blink_for_unit(game_view, unit_map[i][j]))) {
						draw_unit(io, view_config, x, y, unit_map[i][j]);
					}
				}
			} else {
				draw_empty_cell(io, view_config, x, y);
			}
		}
	}
}

void draw_game_view(GameView *game_view)
{
	draw_rectangle(game_view->io, &game_view->view_config, 0, 0, IO_WIDTH, IO_HEIGHT, COL_BACKGROUND, COL_BACKGROUND);
	draw_map(game_view, &game_view->view_config, game_view->io, game_view->game_state, game_view->i_center, game_view->j_center);
	if (game_view->end_of_turn) {
		if (blink_is_on(game_view->blink)) {
			draw_rectangle(game_view->io, &game_view->view_config, IO_WIDTH - 10, IO_HEIGHT - 10, IO_WIDTH, IO_HEIGHT, COL_INFO_TEXT_1, COL_INFO_TEXT_1);
		}
	}
}

