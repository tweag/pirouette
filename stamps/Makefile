hs_files = $(shell ls *.hs *.c)
bin_files = $(patsubst %.c,%.bin,$(hs_files:.hs=.bin))

all: $(bin_files)
	echo $(bin_files)

%haskell.bin: %haskell.hs
	cabal install $@ --overwrite-policy=always

%c.bin: %c.c
	gcc -lz3 -lstdc++ -O3 $< -o $@

results: with-shell-cmd-from-haskell.bin time.sh
	./time.sh

clean:
	rm *.hi
	rm *.o
