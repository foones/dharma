#include "draw.h"

static void draw_rectangle(IO io, Config *config, int x0, int y0, int width, int height, Color outline, Color fill)
{
	int x, y;
	int x1 = x0 + width;
	int y1 = y0 + height;
	for (x = x0; x < x1; x++) {
		for (y = y0; y < y1; y++) {
			if (x == x0 || x == x1 - 1 || y == y0 || y == y1 - 1) {
				io_draw_point(io, x, y, config->palette[outline]);
			} else {
				io_draw_point(io, x, y, config->palette[fill]);
			}
		}
	}
}

static void draw_circle(IO io, Config *config, int x0, int y0, int width, int height, Color fill)
{
	draw_rectangle(io, config, x0 + 10, y0 + 10, width - 20, height - 20, fill, fill);
}

static void draw_terrain(IO io, Config *config, int x, int y, Terrain *terrain)
{
	draw_rectangle(io, config, x, y, config->cell_size, config->cell_size, empty_cell_color, terrain->color);
}

static void draw_unit(IO io, Config *config, int x, int y, Unit *unit)
{
	draw_circle(io, config, x, y, config->cell_size, config->cell_size, unit->tribe->color);
}

static void draw_empty_cell(IO io, Config *config, int x, int y)
{
	draw_rectangle(io, config, x, y, config->cell_size, config->cell_size, empty_cell_color, empty_cell_color);
}

static void draw_map(IO io, GameState *game_state, int i_center, int j_center)
{
	Config *config = &game_state->config; 
	Map *map = &game_state->map; 
	Unit ***unit_map = game_state->unit_map; 

	int i, j;
	int i0, i1, j0, j1;
	int x, y;

	i0 = i_center - config->ncells_height / 2;
	i1 = i0 + config->ncells_height;

	j0 = j_center - config->ncells_width / 2;
	j1 = j0 + config->ncells_width;

	for (i = i0, y = config->map_y0; i < i1; i++, y += config->cell_size) {
		for (j = j0, x = config->map_x0; j < j1; j++, x+= config->cell_size) {
			if (map_valid_pos(map, i, j)) {
				draw_terrain(io, config, x, y, map->terrain[i][j]);
				if (unit_map[i][j] != NULL) {
					draw_unit(io, config, x, y, unit_map[i][j]);
				}
			} else {
				draw_empty_cell(io, config, x, y);
			}
		}
	}
}

void draw_game_state(IO io, GameState *game_state)
{
	int i_center = 0;
	int j_center = 0;
	draw_map(io, game_state, i_center, j_center);
}

