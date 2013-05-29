.PHONY : all clean

all : co

co : co.c mm.h mm.c
	gcc -o co co.c mm.c -Wall -ansi -g -ggdb -pg -O2

clean :
	rm -f *.o

