all:
	dune build src/main.exe
	ln -sf _build/default/src/main.exe turbo-tv
clean:
	dune clean
	rm -rf ./out
	rm -f ./turbo-tv
	rm -f *.dot
