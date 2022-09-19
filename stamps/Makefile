with-shell-cmd-from-haskell: with-shell-cmd-from-haskell.hs
	ghc $<

with-bindings-from-haskell: with-bindings-from-haskell.hs
	ghc $<

results: with-shell-cmd-from-haskell time.sh
	./time.sh
