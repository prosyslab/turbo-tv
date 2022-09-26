all:
	dune build
	ln -sf _build/default/bin/turbo-tv.exe turbo-tv

test: all
	dune test

clean:
	dune clean
	rm -rf ./out
	rm -f ./turbo-tv
	rm -f *.dot
