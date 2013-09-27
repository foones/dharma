#include "io.h"

int io_init(IO *io) {
	if (SDL_Init(SDL_INIT_VIDEO) != 0) {
		fprintf(stderr, "Unable to initialize SDL: %s\n", SDL_GetError());
		return 0;
	}
	atexit(SDL_Quit);
	*io = SDL_SetVideoMode(IO_WIDTH, IO_HEIGHT, 24, SDL_DOUBLEBUF);
	return 1;
}

void io_clear(IO io) {
	SDL_FillRect(io, NULL, SDL_MapRGB(SDL_GetVideoSurface()->format, 0,0,0));
}

void io_draw_point(IO io, int x, int y, int color) {
	if (x < 0 || x >= IO_WIDTH || y < 0 || y >= IO_HEIGHT) return;
	const int bpp = io->format->BytesPerPixel;
	char *p = &((char *)io->pixels)[y * io->pitch + x * bpp];
	if (color) {
		*p++ = 0xff;
		*p++ = 0xff;
		*p++ = 0xff;
	} else {
		*p++ = 0x00;
		*p++ = 0x00;
		*p++ = 0x00;
	}
}

int io_get_key() {
	SDL_Event ev;
	while (SDL_PollEvent(&ev)) {
		switch (ev.type) {
		case SDL_KEYDOWN:
			return ev.key.keysym.sym;
			/*
			if (ev.key.keysym.sym == SDLK_ESCAPE) {
				return -1;
			}
			*/
		}
	}
	return -1;
}

