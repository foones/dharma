#ifndef _CIVMAP_H_
#define _CIVMAP_H_

#include "config.h"
#include "io.h"

typedef struct _terrain {
	char *name;

	int movecost;
	int defense;

	int food;
	int shields;
	int trade;

	Color color;
} Terrain;

typedef struct _map {
	int width;
	int height;
	Terrain ***terrain;
} Map;

extern Terrain *ocean;
extern Terrain *grassland;
extern Color empty_cell_color;

void init_empty_map(Map *m);
int map_valid_pos(Map *m, int i, int j);
int screen_valid_pos(int x, int y);

#endif
