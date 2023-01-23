
compile : lib.mli lib.ml proof_t.mli proof_t.ml proof_j.mli proof_j.ml main.ml
	ocamlfind ocamlopt -o a.out -linkpkg -package zarith,batteries,yojson,atdgen,ppx_deriving.std      lib.mli lib.ml proof_t.mli proof_t.ml proof_j.mli proof_j.ml main.ml 

clean : 
	rm -rf *.cmx *.cmi *.o a.out
run : 
	./a.out
