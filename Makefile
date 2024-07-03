CC = gcc
CFLAGS = -std=c99 -Wall -Werror -g3
CLINK = include/mpc.c include/mathutil.c -ledit -lm

all:
	$(CC) $(CFLAGS) mlispy.c $(CLINK) -o mlispy