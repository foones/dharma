
INCS=io.h civ.h config.h draw.h tribe.h player.h unit.h utils.h action.h
OBJS=civ.c io.c map.c config.c draw.c tribe.c unit.c player.c action.c
co: $(INCS) $(OBJS)
	clang -o co $(OBJS) -I/usr/include/SDL/ -lSDL -g -ggdb -Wall -O3

