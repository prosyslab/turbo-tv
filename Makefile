all:
	dune build bin
	ln -sf _build/default/bin/turbo-tv.exe turbo-tv

test: all
	dune build test
	dune test

clean:
	dune clean
	rm -rf ./out
	rm -f ./turbo-tv
	rm -f *.dot

promote:
	dune promote
