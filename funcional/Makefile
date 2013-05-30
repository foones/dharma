.PHONY : all clean

all : co

#CC=clang
CC=gcc
CFLAGS+= -Wall -ansi -g -ggdb -pg -O2

OBJS=co.o mm.o obj/cons.o
co : ${OBJS} mm.h
	$(CC) -o co $(OBJS)

clean :
	rm -f *.o obj/*.o gmon.out

%.o : %.c
	$(CC) $(CFLAGS) -c $< -o $@ -I.

