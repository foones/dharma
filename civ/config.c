#include "civ.h"
#include "config.h"

void init_config(Config *config)
{
	int i;

	config->cell_size = 40;
	config->map_x0 = 100;
	config->map_y0 = 16;
	config->map_x1 = IO_WIDTH;
	config->map_y1 = IO_HEIGHT;
	config->ncells_width = (config->map_x1 - config->map_x0) / config->cell_size;
	config->ncells_height = (config->map_y1 - config->map_y0) / config->cell_size;

	for (i = 0; i < CIV_MAX_COLORS; i++) {
		config->palette[i] = io_color(255, 0, 255);
	}

	config->palette[COL_EMPTY_CELL] = io_color(40, 40, 40);

	config->palette[COL_GRASSLAND] = io_color(30, 188, 10);
	config->palette[COL_OCEAN] = io_color(30, 188, 10);

	config->palette[COL_TRIBE0] = io_color(0, 0, 80);
	config->palette[COL_TRIBE1] = io_color(80, 0, 0);

}
