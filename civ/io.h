#ifndef _IO_H_
#define _IO_H_

#include "SDL.h"

typedef unsigned long int IOColor;

typedef SDL_Surface *IO;

#define IO_WIDTH	640
#define IO_HEIGHT	480

int io_init(IO *io);
void io_clear(IO io);
void io_draw_point(IO io, int x, int y, IOColor color);
int io_get_key(void);

#define io_update(IO) SDL_Flip((IO))
#define io_sleep(Millisecs) SDL_Delay((Millisecs))

#define io_color(R, G, B) (((R) << 16) | ((G) << 8) | (B))
#define io_color_red(COL) (((COL) >> 16) & 0xff)
#define io_color_green(COL) (((COL) >> 8) & 0xff)
#define io_color_blue(COL) ((COL) & 0xff)

#endif
