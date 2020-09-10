
compile : big.ml  lib.ml main.ml
	ocamlfind ocamlopt -o a.out -linkpkg -package zarith,batteries,yojson,atdgen,ppx_deriving.std big.ml lib.ml main.ml

clean : 
	rm -rf *.cmx *.cmi *.o a.out
run : 
	./a.out
