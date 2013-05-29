.PHONY : all clean

all : co

co : co.c mm.h mm.c
	gcc -o co co.c mm.c -Wall -ansi -g -ggdb -pg

clean :
	rm -f *.o

