hs_files = $(shell ls *.hs *.c)
bin_files = $(patsubst %.c,%.bin,$(hs_files:.hs=.bin))

all: $(bin_files)
	echo $(bin_files)

%haskell.bin: %haskell.hs
	ghc $< -o $@

%c.bin: %c.c
# TODO: I don't know how to have the library be loaded automatically and it's the least of my problems
	gcc -L /nix/store/6bhg9wkxkjp0xcql941a0nyxvqwidvxq-z3-4.8.15-lib/lib/libz3.so -lz3 -lstdc++ $< -o $@

results: with-shell-cmd-from-haskell.bin time.sh
	./time.sh

clean:
	rm *.hi
	rm *.o
