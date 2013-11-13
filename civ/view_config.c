#include <time.h>

#include "civ.h"
#include "view_config.h"

void init_view_config(ViewConfig *view_config)
{
	int i, j;

	view_config->cell_size = 40;
	view_config->map_x0 = 100;
	view_config->map_y0 = 16;
	view_config->map_x1 = IO_WIDTH;
	view_config->map_y1 = IO_HEIGHT;
	view_config->ncells_width = (view_config->map_x1 - view_config->map_x0) / view_config->cell_size;
	view_config->ncells_height = (view_config->map_y1 - view_config->map_y0) / view_config->cell_size;

	for (i = 0; i < CIV_MAX_COLORS; i++) {
		view_config->palette[i] = io_color(255, 0, 255);
	}

	view_config->palette[COL_BACKGROUND] = io_color(0, 0, 0);
	
	view_config->palette[COL_EMPTY_CELL] = io_color(40, 40, 40);

	view_config->palette[COL_GRASSLAND] = io_color(30, 188, 10);
	view_config->palette[COL_OCEAN] = io_color(10, 30, 188);

	view_config->palette[COL_TRIBE0] = io_color(0, 0, 80);
	view_config->palette[COL_TRIBE1] = io_color(80, 0, 0);

	view_config->palette[COL_INFO_TEXT_1] = io_color(255, 255, 255);

	/* Generate a random terrain model */

	srandom(time(NULL));
	unsigned char model[TERRAIN_MODEL_SIZE][TERRAIN_MODEL_SIZE];
	for (i = 0; i < TERRAIN_MODEL_SIZE; i++) {
		for (j = 0; j < TERRAIN_MODEL_SIZE; j++) {
			model[i][j] = random() % 128 + 128;
		}
	}
	for (i = 0; i < TERRAIN_MODEL_SIZE; i++) {
		for (j = 0; j < TERRAIN_MODEL_SIZE; j++) {
			int di, dj;
			int sum = 0;
			int tot = 0;
			for (di = -2; di <= 2; di++) {
				for (dj = -2; dj <= 2; dj++) {
					sum += model[(TERRAIN_MODEL_SIZE + i + di) % TERRAIN_MODEL_SIZE][(TERRAIN_MODEL_SIZE + j + dj) % TERRAIN_MODEL_SIZE];
				}
				tot++;
			}
			view_config->terrain_model[i][j] = (int)((double)sum / (double)tot);
		}
	}

}

