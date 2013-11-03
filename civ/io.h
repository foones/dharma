#ifndef _IO_H_
#define _IO_H_

#include "SDL.h"

typedef unsigned long IOColor;

typedef SDL_Surface *IO;

#define IO_WIDTH	640
#define IO_HEIGHT	480

int io_init(IO *io);
void io_clear(IO io);
void io_draw_point(IO io, int x, int y, IOColor color);
int io_get_key(void);

#define io_color(R, G, B) (((R) << 16) | ((G) << 8) | (B))
#define io_update(IO) SDL_Flip((IO))
#define io_sleep(Millisecs) SDL_Delay((Millisecs))

#endif
