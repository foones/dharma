#include <stdlib.h>
#include "io.h"

#include "math.h"
#include "time.h"

void refresh(IO io)
{
	static int t = 0;
	int i, j;
	t++;
	for (i = 1; i <= IO_WIDTH; i++) {
		for (j = 1; j <= IO_HEIGHT; j++) {
			io_draw_point(io, i, j, (i + j + t) % 2);
		}
	}
}

int main(int argc, char **argv) {
	IO io;

	if (!io_init(&io)) {
		return 1;
	}

	while (1) {
		/* Refresh screen */
		io_update(io);
		refresh(io);

		/* Get input */
		int key = io_get_key();
		if (key == 27) {
			break;
		}
		if (key != -1) {
			printf("%u\n", key % 256);
		}
	}

	return 0;
}

