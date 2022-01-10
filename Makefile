all:
	dune build src/main.exe
	ln -sf _build/default/src/main.exe jstv
clean:
	dune clean
	rm -f ./jstv
	rm -f *.dot
