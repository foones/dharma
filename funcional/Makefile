.PHONY : all clean

all : co

#CC=clang
CC=gcc
CFLAGS+= -Wall -ansi -g -ggdb -pg -O2

OBJS=co.o mm.o objects/cons.o
INCS=mm.h common.h objects/cons.h
co : ${OBJS} $(INCS)
	$(CC) -o co $(OBJS)

clean :
	rm -f *.o objects/*.o gmon.out

%.o : %.c
	$(CC) $(CFLAGS) -c $< -o $@ -I.

