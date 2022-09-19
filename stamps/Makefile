hs_files = $(shell ls *.hs)
bin_files = $(hs_files:.hs=.bin)

all: $(bin_files)
	echo $(bin_files)

%.bin: %.hs
	ghc $< -o $@

results: with-shell-cmd-from-haskell.bin time.sh
	./time.sh

clean:
	rm *.hi
	rm *.o
