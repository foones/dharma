.PHONY : all clean

all : co

#CC=clang
CC=gcc
LDFLAGS+= -pthread
#CFLAGS+= -Wall -ansi -O2 -fno-strict-aliasing -std=c99
CFLAGS+= -Wall -ansi     -fno-strict-aliasing -std=c99

## Debugging
CFLAGS+= -g -ggdb

## Profiling
#CFLAGS+= -pg

#OBJS=co.o mm.o objects/cons.o lexer.o dict.o vm.o protocomp.o
#INCS=mm.h common.h objects/cons.h lexer.h dict.h vm.h protocomp.h
OBJS=co.o mm.o objects/cons.o vm.o lexer.o dict.o ast.o linkedlist.o
INCS=mm.h common.h objects/cons.h vm.h lexer.h dict.h ast.h linkedlist.h
co : ${OBJS} $(INCS)
	$(CC) -o co $(OBJS) $(LDFLAGS)

clean :
	rm -f *.o objects/*.o gmon.out

%.o : %.c
	$(CC) $(CFLAGS) -c $< -o $@ -I.

