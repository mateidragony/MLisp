CC = gcc
CFLAGS = -std=c99 -Wall -Werror 
CLINK = include/mpc.c include/mathutil.c -ledit -lm

all:
	$(CC) $(CFLAGS) main.c $(CLINK) -o main.out