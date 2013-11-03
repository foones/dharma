#ifndef _CIVCONFIG_H_
#define _CIVCONFIG_H_

#define CIV_MAX_COLORS	16384

typedef struct _config {
	int cell_size;
	int map_x0;
	int map_y0;
	int map_x1;
	int map_y1;
	int ncells_width;
	int ncells_height;

	IOColor palette[CIV_MAX_COLORS];
} Config;

typedef unsigned short Color;

#define COL_EMPTY_CELL	0

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

void init_config(Config *config);

#endif
