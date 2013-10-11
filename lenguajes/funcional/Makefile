.PHONY : all clean

all : co

CC=clang
#CC=gcc
CFLAGS+= -Wall -ansi -O2 -fno-strict-aliasing

## Debugging
CFLAGS+= -g -ggdb 

## Profiling
#CFLAGS+= -pg

OBJS=co.o mm.o objects/cons.o lexer.o dict.o vm.o
INCS=mm.h common.h objects/cons.h lexer.h dict.h vm.h object.h
co : ${OBJS} $(INCS)
	$(CC) -o co $(OBJS)

clean :
	rm -f *.o objects/*.o gmon.out

%.o : %.c
	$(CC) $(CFLAGS) -c $< -o $@ -I.

