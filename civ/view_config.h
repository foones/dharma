#ifndef _CIVVIEWCONFIG_H_
#define _CIVVIEWCONFIG_H_

#include "io.h"

#define CIV_MAX_COLORS	16384

#define TERRAIN_MODEL_SIZE 100

typedef struct _view_config {
	int cell_size;
	int map_x0;
	int map_y0;
	int map_x1;
	int map_y1;
	int ncells_width;
	int ncells_height;

	IOColor palette[CIV_MAX_COLORS];

	unsigned char terrain_model[TERRAIN_MODEL_SIZE][TERRAIN_MODEL_SIZE];
} ViewConfig;

typedef struct _viewport {
	int i0;
	int j0;
	int i1;
	int j1;
} Viewport;

typedef unsigned short Color;

#define COL_BACKGROUND	0
#define COL_EMPTY_CELL	1

/* Terrains */
#define COL_GRASSLAND	1001
#define COL_OCEAN	1002

/* Tribes */
#define COL_TRIBE0	2000
#define COL_TRIBE1	2001
#define COL_TRIBE2	2002
#define COL_TRIBE3	2003
#define COL_TRIBE4	2004
#define COL_TRIBE5	2005
#define COL_TRIBE6	2006
#define COL_TRIBE7	2007

/* Information */
#define COL_INFO_TEXT_1	3001

void init_view_config(ViewConfig *view_config);

#endif
