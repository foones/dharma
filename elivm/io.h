#ifndef _IO_H_
#define _IO_H_

#include "SDL.h"

typedef SDL_Surface *IO;

#define IO_WIDTH	640
#define IO_HEIGHT	480

int io_init(IO *io);
void io_clear(IO io);
void io_draw_point(IO io, int x, int y, int color);
int io_get_key();

#define io_update(IO) SDL_Flip((IO))
#define io_sleep(Millisecs) SDL_Delay((Millisecs))

#endif
