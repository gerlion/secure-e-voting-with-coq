
compile : big.ml lib.mli lib.ml ElectionGuard_t.ml ElectionGuard_t.mli ElectionGuard_j.ml ElectionGuard_j.mli main.ml
	ocamlfind ocamlopt -o a.out -linkpkg -package zarith,batteries,yojson,atdgen,ppx_deriving.std big.ml lib.mli lib.ml ElectionGuard_t.mli ElectionGuard_t.ml ElectionGuard_j.mli ElectionGuard_j.ml main.ml

clean : 
	rm -rf *.cmx *.cmi *.o a.out
run : 
	./a.out
