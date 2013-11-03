#include "civ.h"
#include "map.h"

static Terrain _grassland = {
	"Grassland",

	1, /* movecost */
	2, /* defense */

	2, /* food */
	1, /* shields */
	0, /* trade */

	COL_GRASSLAND,
};
Terrain *grassland = &_grassland;

static Terrain _ocean = {
	"Ocean",

	1, /* movecost */
	2, /* defense */

	1, /* food */
	0, /* shields */
	2, /* trade */

	COL_OCEAN, /* color */
};
Terrain *ocean = &_ocean;

Color empty_cell_color = COL_EMPTY_CELL;

void init_empty_map(Map *m)
{
	int i, j;
	m->width = 200;
	m->height = 100;

	m->terrain = (Terrain ***)malloc(sizeof(Terrain **) * m->height);
	for (i = 0; i < m->height; i++) {
		m->terrain[i] = (Terrain **)malloc(sizeof(Terrain *) * m->width);
		for (j = 0; j < m->height; j++) {
			if ((i + j) % 3 == 0) {
				m->terrain[i][j] = ocean;
			} else {
				m->terrain[i][j] = grassland;
			}
		}
	}
}

int map_valid_pos(Map *m, int i, int j)
{
	return 0 <= i && i < m->height && 0 <= j && j < m->width;
}

int screen_valid_pos(int x, int y)
{
	return 0 <= x && x < IO_WIDTH && 0 <= y && y < IO_HEIGHT;
}

