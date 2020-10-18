all: disgard

clean:
	rm -rf disgard *.o

disgard: disgard.o
	gcc disgard.o -o disgard

disgard.o: disgard.c
	gcc $(CFLAGS) -c disgard.c
