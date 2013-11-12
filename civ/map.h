#ifndef _CIVMAP_H_
#define _CIVMAP_H_

#include "view_config.h"
#include "io.h"

typedef int TerrainKind;

#define TERRAIN_KIND_LAND	0
#define TERRAIN_KIND_SEA	1


typedef struct _terrain {
	char *name;

	TerrainKind kind;

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
